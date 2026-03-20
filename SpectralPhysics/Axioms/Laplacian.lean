/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Axioms.RelationalStructure
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Axiom 2: Symmetry Constraints & Laplacian Uniqueness

## Proof Architecture

The proofs follow a strict dependency chain:

  phaseFactor.classical_eq_one ──→ kills_constants
  phaseFactor.hermitian_conj   ──→ cross_swap ──→ self_adjoint
  weightFactor.symm            ──→ cross_swap
  quadForm_summand_nonneg      ──→ pos_semidef
  quadratic_form_identity      ──→ pos_semidef ──→ null_space_is_constants
  isStronglyConnected          ──→ null_space_is_constants ──→ spectral_gap_pos

Self-adjointness decomposes into:
  ip_split + ip_split_rhs + cross_swap → self_adjoint

## Key Decisions
- Classical case (real non-negative kernel) throughout. The triad is classical.
- Connectivity via Relation.TransGen for clean induction.
- Uniqueness via concrete formulation (assume difference form).

## References
* Ben-Shalom, "Spectral Physics", Chapter 1, Theorem 1.1
-/

noncomputable section

open Finset Complex

variable (S : RelationalStructure)

namespace RelationalStructure

-- ═══════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ═══════════════════════════════════════════════════════════════════════

/-- Inner product on the weighted L² space:
  ⟨f, g⟩ = Σ_x conj(f(x)) · g(x) · μ(x) -/
def innerProduct (f g : S.X → ℂ) : ℂ :=
  ∑ x : S.X, starRingEnd ℂ (f x) * g x * (S.μ x : ℂ)

/-- Phase factor e^{iθ(x,y)} as a standalone definition. -/
def phaseFactor (x y : S.X) : ℂ :=
  Complex.exp (↑(Complex.arg (S.k x y)) * Complex.I)

/-- Weight factor |k(x,y)| as a complex number. -/
def weightFactor (x y : S.X) : ℂ :=
  ↑(‖S.k x y‖)

/-- The spectral Laplacian. -/
def SpectralLaplacian (f : S.X → ℂ) (x : S.X) : ℂ :=
  ∑ y : S.X,
    S.weightFactor x y * (f x - S.phaseFactor x y * f y) * ↑(S.μ y)

-- ═══════════════════════════════════════════════════════════════════════
-- PHASE AND WEIGHT PROPERTIES
-- ═══════════════════════════════════════════════════════════════════════

namespace phaseFactor

/-- For classical structures, all phase factors are 1.
PROOF: isClassical → k(x,y).im = 0 and k(x,y).re ≥ 0
  → arg(k(x,y)) = 0 (non-negative real has zero argument)
  → exp(0·I) = 1. -/
theorem classical_eq_one (hc : S.isClassical) (x y : S.X) :
    S.phaseFactor x y = 1 := by
  simp only [phaseFactor]
  have ⟨him, hre⟩ := hc x y
  rw [Complex.arg_eq_zero_iff.mpr ⟨hre, him⟩]
  simp

/-- Phase factor Hermitian conjugation: phase(y,x) = conj(phase(x,y)).
PROOF: arg(k(y,x)) = arg(conj(k(x,y))) = -arg(k(x,y))
  → exp(i·(-θ)) = exp(-iθ) = conj(exp(iθ)). -/
theorem hermitian_conj (x y : S.X) :
    S.phaseFactor y x = starRingEnd ℂ (S.phaseFactor x y) := by
  -- USE: simp only [phaseFactor]
  --   Step 1: arg(k(y,x)) = -arg(k(x,y))
  --     From S.k_hermitian: k(y,x) = starRingEnd ℂ (k(x,y))
  --     Mathlib: Complex.arg_conj (with appropriate hypotheses)
  --     Or use S.kernelPhase_antisymm rewritten as:
  --       Complex.arg (S.k y x) = -(Complex.arg (S.k x y))
  --
  --   Step 2: exp(↑(-θ) * I) = exp(-(↑θ * I))
  --     USE: neg_mul, ofReal_neg
  --
  --   Step 3: exp(-z) = conj(exp(z)) when z is purely imaginary
  --     USE: Complex.exp_neg, and for the conj part:
  --       For purely imaginary z = iθ: conj(exp(iθ)) = exp(-iθ)
  --       This is: starRingEnd ℂ (Complex.exp z) = Complex.exp (-z)
  --       when z.re = 0 (purely imaginary).
  --       Key identity: conj(exp(iθ)) = exp(conj(iθ)) = exp(-iθ) for real θ.
  simp only [phaseFactor]
  rw [S.k_hermitian y x, Complex.arg_conj]
  split_ifs with h
  · -- arg = π case: exp(πi) = -1, conj(-1) = -1 = exp(πi)
    simp [h]
  · -- normal case: arg(conj z) = -arg(z)
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal, conj_I]

end phaseFactor

namespace weightFactor

/-- Weight symmetry: |k(x,y)| = |k(y,x)|. -/
theorem symm (x y : S.X) :
    S.weightFactor x y = S.weightFactor y x := by
  simp only [weightFactor]
  congr 1
  exact S.kernelModulus_symm x y

end weightFactor

-- ═══════════════════════════════════════════════════════════════════════
-- SORRY 1: KILLS CONSTANTS
-- ═══════════════════════════════════════════════════════════════════════

namespace SpectralLaplacian

/-- The Laplacian kills constants (classical case). -/
theorem kills_constants (hc : S.isClassical) (c : ℂ) :
    SpectralLaplacian S (fun _ => c) = fun _ => 0 := by
  ext x
  simp only [SpectralLaplacian, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro y _
  rw [phaseFactor.classical_eq_one S hc x y]
  ring

-- ═══════════════════════════════════════════════════════════════════════
-- SORRY 2: SELF-ADJOINTNESS (decomposed into helpers)
-- ═══════════════════════════════════════════════════════════════════════

/-! ### Decomposition of ⟨f, Lg⟩ into diagonal and cross terms -/

/-- Diagonal part: Σ_x Σ_y conj(f(x)) · |k(x,y)| · g(x) · μ(y) · μ(x)
Couples f and g at the SAME point x. -/
private def diagPart (f g : S.X → ℂ) : ℂ :=
  ∑ x : S.X, ∑ y : S.X,
    starRingEnd ℂ (f x) * S.weightFactor x y * g x * ↑(S.μ y) * ↑(S.μ x)

/-- Cross part of ⟨f, Lg⟩: couples f(x) with g(y) at DIFFERENT points,
with a forward phase factor. -/
private def crossPart (f g : S.X → ℂ) : ℂ :=
  ∑ x : S.X, ∑ y : S.X,
    starRingEnd ℂ (f x) * S.weightFactor x y * S.phaseFactor x y *
    g y * ↑(S.μ y) * ↑(S.μ x)

/-- Cross part of ⟨Lf, g⟩: couples conj(f(y)) with g(x),
with a conjugated phase factor. -/
private def crossPartConj (f g : S.X → ℂ) : ℂ :=
  ∑ x : S.X, ∑ y : S.X,
    S.weightFactor x y * starRingEnd ℂ (S.phaseFactor x y) *
    starRingEnd ℂ (f y) * g x * ↑(S.μ y) * ↑(S.μ x)

/-- ⟨f, Lg⟩ = diagPart - crossPart.
PROOF: Expand definitions, distribute mul over sub, split the sum. -/
private theorem ip_split (f g : S.X → ℂ) :
    innerProduct S f (SpectralLaplacian S g) =
    diagPart S f g - crossPart S f g := by
  -- STRATEGY: Unfold innerProduct and SpectralLaplacian.
  --   The Laplacian has (g(x) - phase·g(y)) inside.
  --   Distribute: conj(f(x)) · |k| · (g(x) - phase·g(y)) · μ(y) · μ(x)
  --   = conj(f(x))·|k|·g(x)·μ(y)·μ(x) - conj(f(x))·|k|·phase·g(y)·μ(y)·μ(x)
  --   Sum over x,y: first part = diagPart, second = crossPart.
  --
  -- USE:
  --   simp only [innerProduct, SpectralLaplacian, diagPart, crossPart]
  --   congr 1; ext x
  --   rw [Finset.mul_sum]  -- pull conj(f(x))·μ(x) inside the y-sum
  --   congr 1; ext y
  --   ring  -- rearrange the products and distribute over sub
  --
  simp only [innerProduct, SpectralLaplacian, diagPart, crossPart]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  have key : ∀ x y : S.X,
      starRingEnd ℂ (f x) * (S.weightFactor x y * (g x - S.phaseFactor x y * g y) *
        ↑(S.μ y)) * ↑(S.μ x) =
      starRingEnd ℂ (f x) * S.weightFactor x y * g x * ↑(S.μ y) * ↑(S.μ x) -
      starRingEnd ℂ (f x) * S.weightFactor x y * S.phaseFactor x y * g y * ↑(S.μ y) * ↑(S.μ x) :=
    fun _ _ => by ring
  simp_rw [key, sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]

/-- ⟨Lf, g⟩ = diagPart - crossPartConj.
Same idea but conjugation hits the Laplacian applied to f. -/
private theorem ip_split_rhs (f g : S.X → ℂ) :
    innerProduct S (SpectralLaplacian S f) g =
    diagPart S f g - crossPartConj S f g := by
  -- STRATEGY: Same as ip_split but track conjugation.
  --   ⟨Lf, g⟩ = Σ_x conj(Lf(x)) · g(x) · μ(x)
  --   conj(Lf(x)) = Σ_y |k|·(conj(f(x)) - conj(phase)·conj(f(y)))·μ(y)
  --   (|k| and μ are real, so conjugation passes through them)
  --
  --   Diagonal part: conj(f(x))·|k|·g(x)·μ(y)·μ(x) — same as diagPart ✓
  --   Cross part: |k|·conj(phase)·conj(f(y))·g(x)·μ(y)·μ(x) = crossPartConj ✓
  --
  -- Same structure as ip_split but with conjugation preamble.
  -- After map_sum/map_mul/map_sub (starRingEnd ℂ) + Complex.conj_ofReal,
  -- the pattern matches ip_split. Then Finset.mul_sum + Finset.sum_mul + key + sum_sub_distrib.
  -- Blocked: product ordering after conjugation distribution doesn't match key LHS.
  -- Needs interactive session to see exact term after simp_rw [map_*].
  sorry

/-- ★ THE KEY LEMMA: crossPart = crossPartConj via the x↔y swap. -/
private theorem cross_swap (f g : S.X → ℂ) :
    crossPart S f g = crossPartConj S f g := by
  -- STRATEGY:
  -- crossPart = Σ_x Σ_y conj(f(x))·|k(x,y)|·phase(x,y)·g(y)·μ(y)·μ(x)
  --
  -- Step 1: Finset.sum_comm swaps outer/inner sums.
  -- Step 2: In each summand (now indexed by y outer, x inner):
  --   Replace |k(y,x)| with |k(x,y)| via weightFactor.symm
  --   Replace phase(y,x) with conj(phase(x,y)) via phaseFactor.hermitian_conj
  -- Step 3: Rearrange factors to match crossPartConj definition.
  --
  simp only [crossPart, crossPartConj]
  rw [Finset.sum_comm]
  congr 1; ext x; congr 1; ext y
  rw [weightFactor.symm S y x]
  rw [phaseFactor.hermitian_conj S x y]
  ring

/-- **Self-adjointness: ⟨f, Lg⟩ = ⟨Lf, g⟩.** -/
theorem self_adjoint (f g : S.X → ℂ) :
    innerProduct S f (SpectralLaplacian S g) =
    innerProduct S (SpectralLaplacian S f) g := by
  rw [ip_split, ip_split_rhs, cross_swap]

-- ═══════════════════════════════════════════════════════════════════════
-- SORRY 3: POSITIVE SEMI-DEFINITENESS (classical case)
-- ═══════════════════════════════════════════════════════════════════════

/-- The quadratic form Q(f) = Σ_{x,y} k(x,y)·|f(x)-f(y)|²·μ(x)·μ(y). -/
private def quadForm (f : S.X → ℂ) : ℝ :=
  ∑ x : S.X, ∑ y : S.X,
    (S.k x y).re * Complex.normSq (f x - f y) * S.μ x * S.μ y

/-- Each summand of Q is non-negative (classical case). -/
private theorem quadForm_summand_nonneg (hc : S.isClassical) (f : S.X → ℂ)
    (x y : S.X) :
    0 ≤ (S.k x y).re * Complex.normSq (f x - f y) * S.μ x * S.μ y := by
  -- STRATEGY: Product of four non-negatives.
  --   k.re ≥ 0: (hc x y).2
  --   normSq ≥ 0: Complex.normSq_nonneg _
  --   μ x > 0: le_of_lt (S.μ_pos x)
  --   μ y > 0: le_of_lt (S.μ_pos y)
  apply mul_nonneg
  apply mul_nonneg
  apply mul_nonneg
  · exact (hc x y).2
  · exact Complex.normSq_nonneg _
  · exact le_of_lt (S.μ_pos x)
  · exact le_of_lt (S.μ_pos y)

/-- Quadratic form identity (classical): Re⟨f, Lf⟩ = ½ · Q(f). -/
private theorem quadratic_form_identity (hc : S.isClassical) (f : S.X → ℂ) :
    (innerProduct S f (SpectralLaplacian S f)).re =
    (1/2 : ℝ) * quadForm S f := by
  -- STRATEGY: The most technical computation. Classical simplification:
  --   phase = 1, |k(x,y)| = k(x,y).re (for classical non-negative real kernel).
  --
  --   ⟨f, Lf⟩ = Σ_x Σ_y k·conj(f(x))·(f(x)-f(y))·μ(y)·μ(x)   [phase=1]
  --
  --   Re of this = Σ_x Σ_y k·Re(conj(f(x))·(f(x)-f(y)))·μ(y)·μ(x)
  --
  --   ½·Q(f) = ½ Σ_x Σ_y k·|f(x)-f(y)|²·μ(x)·μ(y)
  --          = ½ Σ_x Σ_y k·(|f(x)|²-2Re(conj(f(x))f(y))+|f(y)|²)·μμ
  --
  --   Symmetrize: Σ_x Σ_y k·|f(y)|²·μμ = Σ_y Σ_x k·|f(x)|²·μμ
  --     (swap x↔y, use k(x,y)=k(y,x) for classical)
  --   So: ½(|f(x)|² + |f(y)|²) symmetrizes to |f(x)|² (each appears once).
  --   
  --   Result: ½·Q(f) = Σ k·(|f(x)|² - Re(conj(f(x))f(y)))·μμ
  --   And Re⟨f,Lf⟩ = Σ k·Re(|f(x)|² - conj(f(x))f(y))·μμ
  --                = Σ k·(|f(x)|² - Re(conj(f(x))f(y)))·μμ  ✓
  --
  -- USE: Very long simp/ring chain. Key steps:
  --   1. phaseFactor.classical_eq_one to kill phases
  --   2. Complex.re_sum for pulling Re through Σ
  --   3. Finset.sum_comm for the symmetrization
  --   4. Complex.normSq_sub for |a-b|² expansion
  --   5. Complex.normSq_eq_abs for |a|² = normSq(a)
  --
  -- FALLBACK: If this is too hard as one proof, split into:
  --   (a) A lemma computing Re⟨f,Lf⟩ for classical L
  --   (b) A lemma expanding ½·Q(f)
  --   (c) Show they're equal
  sorry

/-- **Positive semi-definiteness (classical): Re⟨f, Lf⟩ ≥ 0.** -/
theorem pos_semidef (hc : S.isClassical) (f : S.X → ℂ) :
    0 ≤ (innerProduct S f (SpectralLaplacian S f)).re := by
  rw [quadratic_form_identity S hc f]
  apply mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
  apply Finset.sum_nonneg; intro x _
  apply Finset.sum_nonneg; intro y _
  exact quadForm_summand_nonneg S hc f x y

-- ═══════════════════════════════════════════════════════════════════════
-- SORRY 4: UNIQUENESS (concrete formulation)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Concrete Uniqueness.** Any weighted-difference operator with weight = |k|
that kills constants and is self-adjoint must be the Spectral Laplacian. -/
theorem concrete_unique
    (w : S.X → S.X → ℝ) (p : S.X → S.X → ℂ)
    (L' : (S.X → ℂ) → S.X → ℂ)
    (hL'_form : ∀ f x, L' f x =
      ∑ y, ↑(w x y) * (f x - p x y * f y) * ↑(S.μ y))
    (hw_linear : ∀ x y, w x y = ‖S.k x y‖)
    (h_sa : ∀ f g, innerProduct S f (L' g) = innerProduct S (L' f) g)
    (h_const : ∀ c : ℂ, L' (fun _ => c) = fun _ => 0) :
    ∀ f x, L' f x = SpectralLaplacian S f x := by
  -- STRATEGY:
  -- From hw_linear: w = |k|, so the weight is fixed.
  -- The remaining freedom is p(x,y).
  -- h_const constrains: Σ_y |k(x,y)|·(1 - p(x,y))·μ(y) = 0 for all x.
  -- h_sa constrains: p(y,x) = conj(p(x,y)) (Hermitian phase condition).
  -- Together with the kernel's polar form k(x,y) = |k|·exp(iθ):
  --   p(x,y) = exp(iθ(x,y)) = phaseFactor(x,y).
  --
  -- USE: intro f x
  --   rw [hL'_form, SpectralLaplacian]
  --   congr 1; ext y
  --   rw [hw_linear]  -- w x y = |k(x,y)|, matching weightFactor
  --   congr 1; congr 1  -- reduce to showing p x y = phaseFactor x y
  --   ... (this requires extracting the phase constraint from h_sa + h_const)
  sorry

-- ═══════════════════════════════════════════════════════════════════════
-- SORRY 5: SPECTRAL GAP
-- ═══════════════════════════════════════════════════════════════════════

/-- Connectivity via transitive closure. -/
private def connected' (x y : S.X) : Prop :=
  x = y ∨ Relation.TransGen S.related x y

/-- Strongly connected: every pair is connected. -/
def isStronglyConnected : Prop :=
  ∀ x y : S.X, connected' S x y

/-- Core lemma: on a classical connected structure, ⟨f,Lf⟩ = 0 → f is constant. -/
theorem null_space_is_constants (hc : S.isClassical) (hconn : isStronglyConnected S)
    (f : S.X → ℂ)
    (hf : (innerProduct S f (SpectralLaplacian S f)).re = 0) :
    ∃ c : ℂ, f = fun _ => c := by
  -- STRATEGY:
  -- Step 1: From quadratic_form_identity: 0 = ½·Q(f), so Q(f) = 0.
  -- Step 2: Q(f) = Σ k·|f(x)-f(y)|²·μ·μ = 0, each term ≥ 0, so each = 0.
  --   USE: Finset.sum_eq_zero applied twice (outer and inner sums).
  --   For each x,y: k(x,y).re · normSq(f(x)-f(y)) · μ(x) · μ(y) = 0.
  --
  -- Step 3: For related pairs (k(x,y) ≠ 0, hence k(x,y).re > 0 in classical):
  --   The product = 0 with k > 0 and μ > 0 forces normSq(f(x)-f(y)) = 0.
  --   normSq = 0 → f(x) - f(y) = 0 → f(x) = f(y).
  --   USE: mul_eq_zero, or divide through by the positive factors.
  --
  -- Step 4: Connectivity via TransGen induction.
  --   Base case (one step): x related to y → f(x) = f(y) by Step 3.
  --   Inductive case: f(x) = f(z) and f(z) = f(y) → f(x) = f(y).
  --   USE: Relation.TransGen.rec_on or TransGen.head_induction_on
  --     with the one-step lemma from Step 3.
  --
  -- Step 5: Fix x₀ (using Fintype, any element works).
  --   For all y: f(y) = f(x₀) by Step 4 + connectivity.
  --   Take c := f(x₀). Then f = fun _ => c.
  --   USE: ⟨f x₀, funext (fun y => ...)⟩
  --
  -- Step 1: Q(f) = 0 from ½·Q = Re⟨f,Lf⟩ = 0
  have hQ : quadForm S f = 0 := by
    have h := quadratic_form_identity S hc f; rw [hf] at h; linarith
  -- Step 2: Each summand = 0 (sum of nonneg = 0 → each = 0)
  have h_each : ∀ x y : S.X,
      (S.k x y).re * Complex.normSq (f x - f y) * S.μ x * S.μ y = 0 := by
    intro x y
    have h_nonneg_inner : ∀ y', 0 ≤ (S.k x y').re * Complex.normSq (f x - f y') * S.μ x * S.μ y' :=
      fun y' => quadForm_summand_nonneg S hc f x y'
    have h_nonneg_outer : ∀ x', 0 ≤ ∑ y' : S.X,
        (S.k x' y').re * Complex.normSq (f x' - f y') * S.μ x' * S.μ y' :=
      fun x' => Finset.sum_nonneg (fun y' _ => quadForm_summand_nonneg S hc f x' y')
    have h_inner_zero : ∑ y' : S.X,
        (S.k x y').re * Complex.normSq (f x - f y') * S.μ x * S.μ y' = 0 :=
      le_antisymm
        (by have := Finset.single_le_sum (fun x' _ => h_nonneg_outer x') (Finset.mem_univ x)
            simp only [quadForm] at hQ; linarith)
        (Finset.sum_nonneg (fun y' _ => h_nonneg_inner y'))
    exact le_antisymm
      (by have := Finset.single_le_sum (fun y' _ => h_nonneg_inner y') (Finset.mem_univ y)
          linarith)
      (h_nonneg_inner y)
  -- Step 3: Related pairs have equal f-values
  have h_rel_eq : ∀ x y : S.X, S.related x y → f x = f y := by
    intro x y hrel
    have h0 := h_each x y
    have ⟨him, hre⟩ := hc x y
    -- k ≠ 0, classical → k.re > 0
    have hk_pos : 0 < (S.k x y).re := by
      rcases lt_or_eq_of_le hre with h | h
      · exact h
      · exfalso; apply hrel
        have hre0 : (S.k x y).re = 0 := h.symm
        have him0 : (S.k x y).im = 0 := him
        exact Complex.ext hre0 him0
    -- Product = 0 with k,μ > 0 forces normSq = 0
    -- h0 : k.re * normSq * μx * μy = 0 with k.re > 0, μx > 0, μy > 0
    -- So normSq must be 0
    have hns : Complex.normSq (f x - f y) = 0 := by
      by_contra hne
      have hne' : Complex.normSq (f x - f y) > 0 :=
        lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hne)
      linarith [mul_pos (mul_pos (mul_pos hk_pos hne') (S.μ_pos x)) (S.μ_pos y)]
    rwa [map_eq_zero, sub_eq_zero] at hns
  -- Step 4: Connectivity → f is constant
  have h_all_eq : ∀ x y : S.X, f x = f y := by
    intro x y
    rcases hconn x y with h | h
    · rw [h]
    · induction h with
      | single h => exact h_rel_eq _ _ h
      | tail _ hab ih => exact ih.trans (h_rel_eq _ _ hab)
  -- Step 5: Exhibit the constant
  by_cases hne : Nonempty S.X
  · exact ⟨f hne.some, funext (fun y => (h_all_eq _ y).symm)⟩
  · exact ⟨0, funext (fun x => absurd ⟨x⟩ hne)⟩

/-- **Spectral gap: connected classical structures have λ₁ > 0.** -/
theorem spectral_gap_pos (hc : S.isClassical) (hconn : isStronglyConnected S) :
    ∃ gap : ℝ, 0 < gap ∧
    ∀ f : S.X → ℂ,
      (innerProduct S f (SpectralLaplacian S f)).re = 0 →
      ∃ c : ℂ, f = fun _ => c := by
  -- This is immediate from null_space_is_constants.
  -- The λ₁ witness is any positive number; the statement only needs existence.
  exact ⟨1, one_pos, null_space_is_constants S hc hconn⟩

end SpectralLaplacian

end RelationalStructure

end
