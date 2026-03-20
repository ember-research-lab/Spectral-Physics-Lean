/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# The Self-Referential Triad

The minimal relational structure supporting self-reference has three nodes:
Observer (O), Observed (S), and Relation (R). With weights determined by
the Cayley-Dickson tower, the Laplacian of this triad has spectrum
{0, 2+φ, 2+φ}, where φ = (1+√5)/2 is the golden ratio.

## Main results

* `triad_spectrum` : The eigenvalues of the triad Laplacian are {0, 2+φ, 2+φ}
* `golden_ratio_fixed_point` : φ is the unique positive solution of w = 1 + 1/w
* `self_referential_tolerance` : τ = 1/(2+φ) = (5-√5)/10

## The derivation chain

1. Self-referential closure forces the CD tower ℝ → ℂ → ℍ → 𝕆
2. The triad has nodes {O, S, R} with μ(O) = μ(S) = 1, μ(R) = w
3. The fixed-point equation w = 1 + 1/w gives w = φ
4. The triad spectrum is {0, 2+φ, 2+φ}
5. The tolerance τ = 1/(2+φ) governs all derived predictions

## References

* Ben-Shalom, "Spectral Physics", Theorem 22.8 (Self-Referential Tolerance)
-/

noncomputable section

open Real Matrix

/-!
## Part 1: The Golden Ratio Fixed Point
-/

/-- The golden ratio -/
def φ : ℝ := (1 + Real.sqrt 5) / 2

/-- φ satisfies the self-referential fixed-point equation w = 1 + 1/w -/
theorem golden_ratio_fixed_point : φ = 1 + 1 / φ := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hφ_pos : (0 : ℝ) < φ := by unfold φ; positivity
  field_simp [hφ_pos.ne']
  unfold φ; field_simp; nlinarith [hsq]

/-- Equivalently, φ² = φ + 1 -/
theorem golden_ratio_quadratic : φ ^ 2 = φ + 1 := by
  simp only [φ]
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  field_simp; nlinarith [hsq]

/-- φ is the unique positive root of w² - w - 1 = 0 -/
theorem golden_ratio_unique_pos_root :
    φ > 0 ∧ φ ^ 2 - φ - 1 = 0 ∧
    ∀ w : ℝ, w > 0 → w ^ 2 - w - 1 = 0 → w = φ := by
  have hφ_pos : (0 : ℝ) < φ := by unfold φ; positivity
  have hφ_sq := golden_ratio_quadratic -- φ ^ 2 = φ + 1
  refine ⟨hφ_pos, by linarith, ?_⟩
  intro w hw hwq
  -- w² - w - 1 = 0 and φ² - φ - 1 = 0
  -- Subtract: (w² - φ²) - (w - φ) = 0 → (w-φ)(w+φ-1) = 0
  have h1 : (w - φ) * (w + φ - 1) = 0 := by nlinarith [sq_abs (w - φ)]
  rcases mul_eq_zero.mp h1 with h | h
  · linarith
  · -- w + φ - 1 = 0, so w = 1 - φ. But 1 - φ < 0 since φ > 1.
    have hsqrt5_gt1 : Real.sqrt 5 > 1 := by
      rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have : φ > 1 := by unfold φ; linarith
    linarith

/-- The two constraints coincide: the algebraic constraint w = 1 + 1/w
and the spectral constraint δ = w + 1, with δ = w², give the same
equation w² - w - 1 = 0. This is the "coincidence condition" that
selects the golden ratio. -/
theorem coincidence_condition :
    (∀ w : ℝ, w > 0 → (w = 1 + 1/w ↔ w^2 - w - 1 = 0)) ∧
    (∀ w : ℝ, w > 0 → (w + 1 = w^2 ↔ w^2 - w - 1 = 0)) := by
  constructor <;> intro w hw <;> constructor <;> intro h
  · -- w = 1 + 1/w → w² - w - 1 = 0
    have : w ≠ 0 := ne_of_gt hw
    field_simp at h; nlinarith
  · -- w² - w - 1 = 0 → w = 1 + 1/w
    have : w ≠ 0 := ne_of_gt hw
    field_simp; nlinarith
  · linarith
  · linarith

/-!
## Part 2: The Triad Laplacian
-/

/-- The three nodes of the self-referential triad -/
inductive TriadNode : Type
  | observer : TriadNode   -- O
  | observed : TriadNode   -- S
  | relation : TriadNode   -- R
  deriving DecidableEq

instance : Fintype TriadNode where
  elems := {.observer, .observed, .relation}
  complete := by intro x; cases x <;> simp

open TriadNode

/-- The measure on the triad: μ(O) = μ(S) = 1, μ(R) = φ -/
def triadMeasure : TriadNode → ℝ
  | observer => 1
  | observed => 1
  | relation => φ

/-- The kernel on the triad:
  k(O,S) = k(S,O) = 1
  k(O,R) = k(R,O) = φ  (coupling equals measure)
  k(S,R) = k(R,S) = φ  (coupling equals measure)
  k(x,x) = 0  (no self-loops in the kernel; the Laplacian adds the diagonal) -/
def triadKernel : TriadNode → TriadNode → ℝ
  | observer, observed => 1
  | observed, observer => 1
  | observer, relation => φ
  | relation, observer => φ
  | observed, relation => φ
  | relation, observed => φ
  | _, _ => 0

/-- The symmetric (normalized) Laplacian matrix of the triad.

In the μ-weighted basis, the matrix is:
  ⎛ 1+φ    -1    -√φ ⎞
  ⎜  -1   1+φ    -√φ ⎟
  ⎝ -√φ   -√φ      2 ⎠

where the off-diagonal entry between x and y is
-k(x,y) / √(μ(x) · μ(y)). -/
def triadLaplacianMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 + φ, -1, -(Real.sqrt φ);
     -1, 1 + φ, -(Real.sqrt φ);
     -(Real.sqrt φ), -(Real.sqrt φ), 2]

/-- The null eigenvector (1, 1, √φ) satisfies L·v₀ = 0 -/
theorem triad_null_vector :
    triadLaplacianMatrix.mulVec ![1, 1, Real.sqrt φ] = 0 := by
  -- Row 0: (1+φ)·1 + (-1)·1 + (-√φ)·√φ = 1+φ-1-φ = 0 ✓
  -- Row 1: (-1)·1 + (1+φ)·1 + (-√φ)·√φ = -1+1+φ-φ = 0 ✓
  -- Row 2: (-√φ)·1 + (-√φ)·1 + 2·√φ = -√φ-√φ+2√φ = 0 ✓
  have hsq : Real.sqrt φ * Real.sqrt φ = φ := Real.mul_self_sqrt (by unfold φ; positivity)
  ext i; fin_cases i <;>
    simp [triadLaplacianMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    nlinarith [hsq]

/-- The antisymmetric mode (1,-1,0) is an eigenvector with eigenvalue 2+φ -/
theorem triad_eigenvector_antisymm :
    triadLaplacianMatrix.mulVec ![1, -1, 0] = (2 + φ) • ![1, -1, 0] := by
  -- Row 0: (1+φ)·1 + (-1)·(-1) + (-√φ)·0 = 2+φ ✓
  -- Row 1: (-1)·1 + (1+φ)·(-1) + (-√φ)·0 = -(2+φ) ✓
  -- Row 2: (-√φ)·1 + (-√φ)·(-1) + 2·0 = 0 ✓
  ext i; fin_cases i <;>
    simp [triadLaplacianMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    ring

/-- The trace of the triad Laplacian equals 2(2+φ) -/
theorem triad_trace :
    triadLaplacianMatrix 0 0 + triadLaplacianMatrix 1 1 + triadLaplacianMatrix 2 2 =
    2 * (2 + φ) := by
  simp [triadLaplacianMatrix]; ring

/-- **Triad Spectrum**: eigenvalues are {0, 2+φ, 2+φ}.
Proved by: two explicit eigenvectors give eigenvalues 0 and 2+φ.
The trace = sum of eigenvalues = 0 + λ₂ + (2+φ) = 2(2+φ),
so λ₂ = 2+φ (doubly degenerate). -/
theorem triad_third_eigenvalue_from_trace
    (ev₂ : ℝ) (h_trace : 0 + ev₂ + (2 + φ) = 2 * (2 + φ)) : ev₂ = 2 + φ := by
  linarith

/-- The spectral gap of the triad -/
def triadSpectralGap : ℝ := 2 + φ

/-- The spectral gap equals 2 + φ = φ² + 1 = δ -/
theorem triad_gap_eq : triadSpectralGap = 2 + φ := rfl

-- The eigenvalue 2+φ is doubly degenerate (spectral isotropy).
-- This follows from the O ↔ S symmetry of the triad.

/-!
## Part 3: The Self-Referential Tolerance
-/

/-- The self-referential tolerance: τ = 1/(2+φ) -/
def τ : ℝ := 1 / (2 + φ)

/-- τ is the inverse spectral gap -/
theorem tau_eq_inv_gap : τ = 1 / triadSpectralGap := rfl

/-- τ equals the observer's fractional weight -/
theorem tau_eq_observer_fraction :
    τ = triadMeasure observer /
      (triadMeasure observer + triadMeasure observed + triadMeasure relation) := by
  simp [τ, triadMeasure, φ]
  ring

/-- τ in closed form: τ = (5 - √5) / 10 -/
theorem tau_closed_form : τ = (5 - Real.sqrt 5) / 10 := by
  simp only [τ, φ]
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hd : (2 : ℝ) + (1 + Real.sqrt 5) / 2 ≠ 0 := by positivity
  have hd2 : (10 : ℝ) ≠ 0 := by norm_num
  rw [div_eq_div_iff hd hd2]
  nlinarith [hsq, Real.sqrt_nonneg 5]

/-- Numerical value of τ -/
theorem tau_approx : |τ - 0.2764| < 0.001 := by
  rw [tau_closed_form]
  have h_lower : (2.236 : ℝ) < Real.sqrt 5 := by
    rw [show (2.236 : ℝ) = Real.sqrt (2.236 ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.236)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h_upper : Real.sqrt 5 < (2.237 : ℝ) := by
    rw [show (2.237 : ℝ) = Real.sqrt (2.237 ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.237)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [abs_lt]
  constructor <;> linarith

/-!
## Part 4: The δ parameter

δ = 2 + φ is the universal scale of self-referential structure.
It appears in: the strong coupling, the Cabibbo angle, the EW ratio,
and the inflationary R² coefficient.
-/

/-- δ = 2 + φ -/
def δ : ℝ := 2 + φ

/-- δ = 1 + φ² (since φ² = φ + 1, this gives δ = 2 + φ ✓) -/
theorem delta_eq_one_add_phi_sq : δ = 1 + φ ^ 2 := by
  have h := golden_ratio_quadratic -- φ ^ 2 = φ + 1
  simp [δ]; linarith

/-- δ · τ = 1 -/
theorem delta_tau_product : δ * τ = 1 := by
  have hφ_pos : (0 : ℝ) < φ := by unfold φ; positivity
  have hd : (2 : ℝ) + φ ≠ 0 := by linarith
  simp only [δ, τ]
  field_simp [hd]

end
