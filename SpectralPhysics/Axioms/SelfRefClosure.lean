/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Axioms.Laplacian
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.Interval.Finset.Fin

/-
  Axioms/SelfRefClosure.lean — Abstract Axiom 3 (Self-Referential Closure)

  The most abstract formulation of Axiom 3, independent of any specific
  application. The core principle:

    "If a structure is type-compatible with the algebra,
     it is detectable by the functional. Nothing compatible can hide."

  This file provides:
  1. The abstract algebraic framework (StarAlgebraWithState)
  2. The three conditions of Axiom 3 as independent typeclasses
  3. Algebraic closure (meta-observation terminates)
  4. The completeness theorem: closure + faithfulness => no ghosts
  5. Stability above the complexity threshold I*
  6. Instance: Spectral physics (trace on observation algebra)
  7. Abstract interface for external instances (Hodge, etc.)

  Dependencies: Axioms/RelationalStructure, Axioms/Laplacian

  References:
    Manuscript v0.8, lines 285-304 (Axiom 3)
    Manuscript v0.8, lines 5485-5491 (Algebraic closure definition)
-/

-- ============================================================================
-- SECTION 0: THE ABSTRACT PRINCIPLE
-- ============================================================================

/-
  The abstract content of Axiom 3, stripped of all physics:

  Given:
    - An algebra A (with involution *)
    - A positive linear functional w : A -> R

  Faithfulness: w(a* a) > 0 for every nonzero a
  Completeness: the algebra contains everything type-compatible
  Detection: faithfulness + completeness => nothing type-compatible
             is a ghost (present but invisible)
-/

/-- A *-algebra over R with a positive linear functional (state). -/
class StarAlgebraWithState (A : Type*) extends Mul A, Add A, Star A, Zero A where
  /-- The state functional w : A -> R -/
  state : A → ℝ
  /-- w is positive: w(a* a) >= 0 -/
  state_nonneg : ∀ a : A, state (star a * a) ≥ 0
  /-- w is nondegenerate -/
  state_nonzero : ∃ a : A, state (star a * a) > 0

-- ============================================================================
-- SECTION 1: THE THREE CONDITIONS (INDEPENDENT TYPECLASSES)
-- ============================================================================

/-
  Axiom 3 decomposes into three logically independent conditions.
  Different downstream theorems use different conditions:

  - Division algebra forcing: AlgebraicallyClosed
  - Gap inheritance (alpha_s, Lambda_cosmo): SectorFaithful
  - Spectral convergence non-collapse: TraceFaithful
  - Spectrum recovery: SpectralDetermination
-/

/-- The spectral data of a self-adjoint operator. -/
structure SpectralData (n : ℕ) where
  /-- Eigenvalues, indexed -/
  eigenvalues : Fin n → ℝ
  /-- Eigenvalues are non-negative (from Axiom 2: L >= 0) -/
  eigenvalues_nonneg : ∀ i, eigenvalues i ≥ 0
  /-- Eigenvalues are sorted -/
  eigenvalues_sorted : ∀ i j, i ≤ j → eigenvalues i ≤ eigenvalues j

variable {n : ℕ}

/-- The trace functional: Tr(g(L)) = sum g(lambda_k). -/
def spectralTrace (S : SpectralData n) (g : ℝ → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun i => g (S.eigenvalues i))

/--
  Condition (i): DETERMINATION

  The map g |-> Tr(g(L)) determines the spectrum {lambda_k}.

  Finite dim: theorem (Newton's identities).
  Infinite dim: genuine constraint (forces compact resolvent).
-/
class SpectralDetermination (S : SpectralData n) : Prop where
  determines : ∀ S' : SpectralData n,
    (∀ g : ℝ → ℝ, spectralTrace S g = spectralTrace S' g) →
    S.eigenvalues = S'.eigenvalues

/--
  Condition (ii): POSITIVITY / FAITHFULNESS

  The trace defines a faithful state on the observation algebra.
  For every nonzero a in A_obs, w(a*a) > 0.

  GNS language: w is faithful, pi_w is injective.
-/
class TraceFaithful (A : Type*) [StarAlgebraWithState A] : Prop where
  pos : ∀ a : A, a ≠ 0 → StarAlgebraWithState.state (star a * a) > 0

/--
  Condition (iii): SECTOR FAITHFULNESS

  For A = A_1 tensor A_2 tensor ... tensor A_k, partial traces are faithful
  on each individual factor.

  Strictly stronger than (ii). No sector hides behind others.
-/
class SectorFaithful
    (A₁ A₂ A₃ : Type*)
    [StarAlgebraWithState A₁] [StarAlgebraWithState A₂] [StarAlgebraWithState A₃]
    : Prop where
  factor1_faithful : TraceFaithful A₁
  factor2_faithful : TraceFaithful A₂
  factor3_faithful : TraceFaithful A₃

-- ============================================================================
-- SECTION 2: ALGEBRAIC CLOSURE
-- ============================================================================

/-
  The algebraic closure condition (Ch 22, line 5485):
  Meta-observation generates no new structure.

  Independent of conditions (i)-(iii). Constrains the algebra A
  itself, not the pair (A, w).
-/

/-- An algebra supports meta-observation. -/
class MetaObservable (A : Type*) where
  /-- The meta-observation extension -/
  metaExtend : Type*
  /-- A embeds into its extension -/
  embed : A → metaExtend

/-- Algebraic closure: meta-observation terminates. -/
class AlgebraicallyClosed (A : Type*) [MetaObservable A] : Prop where
  closed : Nonempty (MetaObservable.metaExtend (A := A) ≃ A)

-- ============================================================================
-- SECTION 3: THE COMPLETENESS PRINCIPLE
-- ============================================================================

/--
  Algebraic closure + faithfulness => no ghosts.

  Trivial given the premises. The content is in establishing
  the premises for specific instances.
-/
theorem completeness_no_ghosts
    (A : Type*) [StarAlgebraWithState A] [MetaObservable A]
    [AlgebraicallyClosed A] [hf : TraceFaithful A] :
    ∀ a : A, a ≠ 0 → StarAlgebraWithState.state (star a * a) > 0 :=
  fun a ha => hf.pos a ha

-- ============================================================================
-- SECTION 4: STABILITY ABOVE THE COMPLEXITY THRESHOLD
-- ============================================================================

/-
  Phase transition:
  - Below I*: faithfulness fragile
  - At transition: unstable
  - Above I*: stable, self-correcting (spectral gap -> exponential recovery)
-/

/-- Integration capacity: spectral complexity measure. -/
noncomputable def integrationCapacity (S : SpectralData n) : ℝ :=
  spectralTrace S (fun x => if x > 0 then 1 / x else 0)

/-- The complexity threshold I*. -/
class ComplexityThreshold (n : ℕ) where
  iStar : ℝ
  iStar_pos : iStar > 0

/-- Above I*, faithfulness is stable under perturbation.
    Requires n >= 2 so that the first nonzero eigenvalue exists. -/
class StableFaithfulness (S : SpectralData n) (A : Type*)
    [StarAlgebraWithState A] [ComplexityThreshold n] (hn : n ≥ 2) : Prop where
  above_threshold : integrationCapacity S > ComplexityThreshold.iStar (n := n)
  faithful : TraceFaithful A
  spectral_gap_pos : S.eigenvalues ⟨1, by omega⟩ > 0

-- ============================================================================
-- SECTION 5: THE FULL AXIOM
-- ============================================================================

/-- Self-Referential Closure (Axiom 3): conjunction of all conditions.
    Import individual conditions when possible. -/
class SelfRefClosure
    (S : SpectralData n)
    (A : Type*)
    [StarAlgebraWithState A] [MetaObservable A] : Prop where
  determination : SpectralDetermination S
  faithfulness : TraceFaithful A
  sectorFaithful : ∃ (A₁ A₂ A₃ : Type*)
    (_ : StarAlgebraWithState A₁)
    (_ : StarAlgebraWithState A₂)
    (_ : StarAlgebraWithState A₃),
    SectorFaithful A₁ A₂ A₃
  closure : AlgebraicallyClosed A

-- ============================================================================
-- SECTION 6: SPECTRAL PHYSICS INSTANCE
-- ============================================================================

/-- **Sorted sequences with equal counting functions are equal.**
For f, g : Fin n → ℝ both sorted (monotone), if for all a ∈ ℝ
the number of indices k with f(k) ≤ a equals the number with g(k) ≤ a,
then f = g pointwise.

Proof: by contradiction. If f(i) ≠ g(i) at some i, WLOG f(i) < g(i).
Take a = f(i). Then #{k : f(k) ≤ a} ≥ i+1 (sorted: k ≤ i ⟹ f(k) ≤ f(i) = a).
But #{k : g(k) ≤ a} ≤ i (sorted: k ≥ i ⟹ g(k) ≥ g(i) > a). Contradiction. -/
private theorem sorted_eq_of_count_eq
    (f g : Fin n → ℝ)
    (hf : ∀ i j : Fin n, i ≤ j → f i ≤ f j)
    (hg : ∀ i j : Fin n, i ≤ j → g i ≤ g j)
    (h_count : ∀ a : ℝ,
      Finset.card (Finset.univ.filter (fun k : Fin n => f k ≤ a)) =
      Finset.card (Finset.univ.filter (fun k : Fin n => g k ≤ a))) :
    f = g := by
  ext i
  by_contra h_ne
  rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
  · -- f(i) < g(i): take a = f(i)
    have h := h_count (f i)
    -- Lower bound on #{k : f(k) ≤ f(i)}: contains all k ≤ i (sorted)
    have h_sub : Finset.Iic i ⊆
        Finset.univ.filter (fun k : Fin n => f k ≤ f i) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hf k i (Finset.mem_Iic.mp hk)
    -- Upper bound on #{k : g(k) ≤ f(i)}: excludes all k ≥ i (sorted + g(i) > f(i))
    have h_sub' : Finset.univ.filter (fun k : Fin n => g k ≤ f i) ⊆
        Finset.Iio i := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simp only [Finset.mem_Iio]
      by_contra h_ge
      push_neg at h_ge
      exact not_le.mpr h_lt (le_trans (hg i k h_ge) hk)
    have h1 := Finset.card_le_card h_sub
    have h2 := Finset.card_le_card h_sub'
    simp only [Fin.card_Iic, Fin.card_Iio] at h1 h2
    omega
  · -- g(i) < f(i): symmetric
    have h := h_count (g i)
    have h_sub : Finset.Iic i ⊆
        Finset.univ.filter (fun k : Fin n => g k ≤ g i) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hg k i (Finset.mem_Iic.mp hk)
    have h_sub' : Finset.univ.filter (fun k : Fin n => f k ≤ g i) ⊆
        Finset.Iio i := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simp only [Finset.mem_Iio]
      by_contra h_ge
      push_neg at h_ge
      exact not_le.mpr h_gt (le_trans (hf i k h_ge) hk)
    have h1 := Finset.card_le_card h_sub
    have h2 := Finset.card_le_card h_sub'
    simp only [Fin.card_Iic, Fin.card_Iio] at h1 h2
    omega

/-- In finite dimensions, determination is a theorem.

The hypothesis `∀ g, Σ g(λ_k) = Σ g(λ'_k)` for ALL g : ℝ → ℝ is very strong.
Specializing to `g(x) = (x - c)^2` and setting `c = S.eigenvalues i` gives
`Σ_k (S.eigenvalues k - S.eigenvalues i)^2 = Σ_k (S'.eigenvalues k - S.eigenvalues i)^2`.
The k = i term on the LHS is 0. Combined with non-negativity and sorting,
this forces `S'.eigenvalues i = S.eigenvalues i`. -/
theorem spectral_determination_finite (S : SpectralData n) :
    SpectralDetermination S := by
  constructor
  intro S' hg
  -- Use sorted_eq_of_count_eq: sorted sequences with equal counting functions are equal.
  -- Get counting function equality from hg with indicator functions.
  apply sorted_eq_of_count_eq S.eigenvalues S'.eigenvalues
    S.eigenvalues_sorted S'.eigenvalues_sorted
  intro a
  -- Specialize hg to g(x) = if x ≤ a then 1 else 0
  have h := hg (fun x => if x ≤ a then 1 else 0)
  simp only [spectralTrace, Finset.sum_boole] at h
  exact_mod_cast h

/-- Gap inheritance: sector faithfulness propagates individual sector gaps. -/
theorem gap_inheritance
    {A₁ A₂ A₃ : Type*}
    [StarAlgebraWithState A₁] [StarAlgebraWithState A₂] [StarAlgebraWithState A₃]
    [sf : SectorFaithful A₁ A₂ A₃]
    (a : A₁) (ha : a ≠ 0) :
    StarAlgebraWithState.state (star a * a) > 0 :=
  sf.factor1_faithful.pos a ha

-- ============================================================================
-- SECTION 7: ABSTRACT INTERFACE FOR EXTERNAL INSTANCES
-- ============================================================================

/-
  Any instance of the completeness principle must provide:
  1. An algebra A (the "algebraic side")
  2. A functional w on A (the "detection mechanism")
  3. A proof of algebraic closure (the algebra is complete)
  4. A proof (or conjecture) of faithfulness (the functional detects all)

  Instances: Hodge.lean, and potentially Langlands.lean,
  RiemannHypothesis.lean, PvsNP.lean.
-/

/-- A Completeness Instance packages all data for the principle. -/
structure CompletenessInstance where
  Algebra : Type*
  algState : StarAlgebraWithState Algebra
  metaObs : MetaObservable Algebra
  isClosed : @AlgebraicallyClosed Algebra metaObs
  isFaithful : @TraceFaithful Algebra algState
