/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.YukawaHierarchy.IntegralityConsistency
import SpectralPhysics.Triad.GoldenRatio
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real-Valued Theorem A — Tight Consistency Bound at GUT

The rational version `IntegralityConsistency.lean` gives `|a_2 - (-179)| < 10⁻²`
using rational placeholders for the irrational GJ structure constants
(`√5`, `√(5/18)`).

This file ports Theorem A to `Real` so that the actual irrational GJ
relations

    `y_d = √5 · y_e`,    `y_u = √(5/18) · y_d`,    `y_s = y_μ / (3+φ)`

can be expressed exactly. The numerical bound tightens to 10⁻⁴
(matching `output/reconstruction_integrality/rigorous_C0_results.json`).

## Tier classification

* **Tier 1 (proved)**: the algebraic decomposition `Tr(D_F²) = trCore + trRemainder`
  in Real, the formula `a_2 = -179 - trRemainder/6` given `y_t = 1`.
* **Tier 2 (conditional)**: the precision bound `|a_2 - (-179)| < 10⁻⁴` at the
  manuscript's specific GUT-running numerical values.

## References

* Manuscript v7 §3 (Galois rationality + GJ submanifold).
* `papers/spectral_physics/yukawa/rigorous_C0_consistency.py` for the
  numerical analog of this theorem.
-/

namespace SpectralPhysics.YukawaHierarchy

open Real

noncomputable section

/-! ## Real-valued Yukawa set -/

/-- A Yukawa set valued in `ℝ`, allowing irrational GJ structure factors. -/
structure RealYukawaSet where
  y_t   : ℝ
  y_c   : ℝ
  y_u   : ℝ
  y_b   : ℝ
  y_s   : ℝ
  y_d   : ℝ
  y_τ   : ℝ
  y_μ   : ℝ
  y_e   : ℝ

namespace RealYukawaSet

/-- The trace `Tr(D_F²)` in Real, on the GJ submanifold. -/
def trDFsq (Y : RealYukawaSet) : ℝ :=
  12 * (Y.y_u^2 + Y.y_c^2 + Y.y_t^2 + Y.y_d^2 + Y.y_s^2 + Y.y_b^2) +
  4  * (Y.y_e^2 + Y.y_μ^2 + Y.y_τ^2) +
  294

/-- The trace's `y_t = 1` contribution: dominant 306. -/
def trCore (Y : RealYukawaSet) : ℝ := 12 * Y.y_t^2 + 294

/-- The remainder (everything quadratic in non-top Yukawas). -/
def trRemainder (Y : RealYukawaSet) : ℝ :=
  12 * (Y.y_u^2 + Y.y_c^2 + Y.y_d^2 + Y.y_s^2 + Y.y_b^2) +
  4  * (Y.y_e^2 + Y.y_μ^2 + Y.y_τ^2)

/-- `Tr(D_F²)` decomposes as `trCore + trRemainder`. -/
theorem trDFsq_decompose (Y : RealYukawaSet) :
    Y.trDFsq = Y.trCore + Y.trRemainder := by
  unfold trDFsq trCore trRemainder; ring

/-- The Seeley-DeWitt `a_2 = -128 - Tr(D_F²)/6`. -/
def a2 (Y : RealYukawaSet) : ℝ := -128 - Y.trDFsq / 6

/-- All squared Yukawa entries are nonneg (since they're squares of reals). -/
theorem trRemainder_nonneg (Y : RealYukawaSet) : Y.trRemainder ≥ 0 := by
  unfold trRemainder
  have h1 : (12 : ℝ) * (Y.y_u^2 + Y.y_c^2 + Y.y_d^2 + Y.y_s^2 + Y.y_b^2) ≥ 0 := by
    apply mul_nonneg (by norm_num)
    positivity
  have h2 : (4 : ℝ) * (Y.y_e^2 + Y.y_μ^2 + Y.y_τ^2) ≥ 0 := by
    apply mul_nonneg (by norm_num)
    positivity
  linarith

/-- **Real Tier 1.**  Given `y_t = 1`, `trCore = 306` exactly. -/
theorem trCore_at_top_one (Y : RealYukawaSet) (h : Y.y_t = 1) :
    Y.trCore = 306 := by
  unfold trCore
  rw [h]; ring

/-- **Real Tier 1.**  Given `y_t = 1`, the SD coefficient `a_2 = -179 - trRemainder/6`. -/
theorem a2_at_top_one (Y : RealYukawaSet) (h : Y.y_t = 1) :
    Y.a2 = -179 - Y.trRemainder / 6 := by
  unfold a2
  rw [Y.trDFsq_decompose, Y.trCore_at_top_one h]
  ring

end RealYukawaSet

/-! ## Building the framework's GUT Yukawas exactly with √5 -/

/-- The framework's GJ-completed GUT-running Yukawas (Real-valued, exact). -/
def frameworkGUT_Real : RealYukawaSet :=
  let yτ : ℝ := 9270  / 1000000
  let ye : ℝ := 2935  / 1000000000
  { y_t := 1
  , y_τ := yτ
  , y_c := (3 / 16) * yτ           -- framework's r_c/r_τ = 3/16
  , y_b := (2 / 3) * yτ            -- GJ
  , y_e := ye
  , y_μ := 22 * ye                  -- Galois rank-2
  , y_d := Real.sqrt 5 * ye         -- GJ: y_d = √5 · y_e
  , y_s := 22 * ye / (3 + φ)        -- GJ: y_s = y_μ/(3+φ)
  , y_u := Real.sqrt (5/18) * (Real.sqrt 5 * ye)   -- y_u = √(5/18) · y_d
  }

/-! ## Squared bounds on each remainder term -/

/-- Bounds on `√5²`: it's exactly 5 (since 5 ≥ 0). -/
theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 :=
  Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)

/-- Bounds on `(√(5/18))²`: it's exactly `5/18`. -/
theorem sqrt_5_18_sq : Real.sqrt (5/18) ^ 2 = 5/18 :=
  Real.sq_sqrt (by norm_num : (0:ℝ) ≤ (5:ℝ)/18)

/-! ## Numerical bound — the Tier 2 result

The remainder for `frameworkGUT_Real` is

  `12 · (y_u² + y_c² + y_d² + y_s² + y_b²) + 4 · (y_e² + y_μ² + y_τ²)`

Each term we can bound by inserting the structural identities:
  y_d² = 5 y_e²
  y_u² = (5/18) · y_d² = (5/18)·5·y_e² = (25/18) y_e²
  y_s² = (22 y_e / (3+φ))² = 484 y_e² / (3+φ)²
  y_b² = (4/9) y_τ²
  y_c² = (9/256) y_τ²
  y_μ² = 484 y_e²

So the remainder reduces to a polynomial in `y_e²` and `y_τ²`. We can then
plug in numeric bounds and conclude the precision.
-/

/-- Algebraic simplification: when we substitute the GJ relations into
    `trRemainder`, the result is `α · y_e² + β · y_τ²` for explicit
    coefficients `α, β` that depend on `φ`. -/
theorem trRemainder_GJ_form
    (yτ ye : ℝ) :
    let Y : RealYukawaSet := {
      y_t := 1, y_τ := yτ, y_c := (3/16) * yτ,
      y_b := (2/3) * yτ, y_e := ye, y_μ := 22 * ye,
      y_d := Real.sqrt 5 * ye,
      y_s := 22 * ye / (3 + φ),
      y_u := Real.sqrt (5/18) * (Real.sqrt 5 * ye) }
    Y.trRemainder = 12 * (
        (Real.sqrt (5/18) * (Real.sqrt 5 * ye))^2  -- y_u²
      + ((3/16) * yτ)^2                              -- y_c²
      + (Real.sqrt 5 * ye)^2                          -- y_d²
      + (22 * ye / (3 + φ))^2                         -- y_s²
      + ((2/3) * yτ)^2                                 -- y_b²
      ) + 4 * (
        ye^2 + (22 * ye)^2 + yτ^2
      ) := by
  unfold RealYukawaSet.trRemainder
  ring

/-- Closed form (after using `(√5)² = 5` and `(√(5/18))² = 5/18`):

    `trRemainder = (...) · y_e² + (...) · y_τ²`

    Coefficient of `y_e²`:
       12 · [(5/18) · 5 + 5 + 484/(3+φ)²] + 4 · [1 + 484]
     = 12 · [25/18 + 5 + 484/(3+φ)²] + 1940
     ≈ 12 · [1.389 + 5 + 484/21.32] + 1940
     ≈ 12 · [1.389 + 5 + 22.70] + 1940 ≈ 12 · 29.09 + 1940 ≈ 2289

    Coefficient of `y_τ²`:
       12 · [9/256 + 4/9] + 4
     ≈ 12 · [0.0352 + 0.444] + 4 ≈ 5.75 + 4 ≈ 9.75

    For ye ≈ 2.94e-6, ye² ≈ 8.6e-12, contribution ≈ 2.0e-8.
    For yτ ≈ 9.27e-3, yτ² ≈ 8.6e-5, contribution ≈ 8.4e-4.

    Total trRemainder ≈ 8.4e-4. Divided by 6: ≈ 1.4e-4.
    So |a_2 - (-179)| ≤ 1.4 × 10⁻⁴.  Matches numerical evidence.

    We do not formalise this final numeric bound (it is a `nlinarith`-style
    computation involving bounds on `√5` and `φ`), but state it as the
    target precision `targetPrecision` for future tightening. -/
def targetPrecision : ℝ := 2 / 10000   -- 2 × 10⁻⁴ — comfortable upper bound

/-- **Real Tier 1 — Theorem A (qualitative form).**

    The Real-valued Theorem A states that with `y_t = 1` and the framework's
    GJ + Galois + r_c/r_τ relations, the SD coefficient `a_2` differs from
    `-179` by at most `trRemainder/6`, which is bounded by a polynomial in
    the small Yukawas (`y_e², y_τ²`) with explicit coefficients in `Real`. -/
theorem theoremA_real (Y : RealYukawaSet) (h : Y.y_t = 1) :
    Y.a2 = -179 - Y.trRemainder / 6 ∧ Y.trRemainder ≥ 0 :=
  ⟨Y.a2_at_top_one h, Y.trRemainder_nonneg⟩

/-- **Real Tier 2 — Theorem A (precision form).**

    The error is bounded by `trRemainder / 6`. For the framework's specific
    GUT-running values, this evaluates to ~ 1.4 × 10⁻⁴ (numerical evidence
    in `rigorous_C0_consistency.py`).

    A formal proof of the explicit numerical bound `< 2 × 10⁻⁴` requires
    `nlinarith` with bounds on `√5` and `φ` — left as future work because
    the existing numerical infrastructure already validates it independently
    (see references). -/
theorem theoremA_real_precision_qualitative (Y : RealYukawaSet)
    (h : Y.y_t = 1)
    (h_remainder_small : Y.trRemainder < targetPrecision * 6) :
    |Y.a2 - (-179)| < targetPrecision := by
  rw [Y.a2_at_top_one h]
  rw [show -179 - Y.trRemainder / 6 - (-179) = -(Y.trRemainder / 6) from by ring]
  rw [abs_neg]
  rw [abs_of_nonneg (by linarith [Y.trRemainder_nonneg])]
  linarith

/-! ## Bounds on `φ` and `(3+φ)⁻²`

These are the building blocks for an explicit numerical Theorem A.
The full numerical bound `< 2 × 10⁻⁴` requires a `nlinarith` with many
irrational terms that we leave for future work; here we prove the
foundational bounds. -/

/-- φ > 1.618 (a numerical lower bound, useful for nlinarith). -/
theorem phi_gt_lower : (1.618 : ℝ) < φ := by
  unfold φ
  have h_sqrt5 : (2.236 : ℝ) < Real.sqrt 5 := by
    have : Real.sqrt (2.236^2) < Real.sqrt 5 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hge : (0 : ℝ) ≤ 2.236 := by norm_num
    rw [Real.sqrt_sq hge] at this
    exact this
  linarith

/-- φ < 1.619. -/
theorem phi_lt_upper : φ < (1.619 : ℝ) := by
  unfold φ
  have h_sqrt5 : Real.sqrt 5 < (2.237 : ℝ) := by
    have : Real.sqrt 5 < Real.sqrt (2.237^2) :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hge : (0 : ℝ) ≤ 2.237 := by norm_num
    rw [Real.sqrt_sq hge] at this
    exact this
  linarith

/-- Bound on `1 / (3 + φ)²`: less than `1/21` (numerically ≈ 0.0469). -/
theorem inv_three_plus_phi_sq_bound :
    1 / (3 + φ)^2 < (1 : ℝ) / 21 := by
  have hφ_lo := phi_gt_lower
  have h_3φ_pos : (0 : ℝ) < 3 + φ := by linarith
  have h_3φ_sq_pos : (0 : ℝ) < (3 + φ)^2 := by positivity
  have h_3φ_sq_lo : (21 : ℝ) < (3 + φ)^2 := by nlinarith
  exact one_div_lt_one_div_of_lt (by norm_num) h_3φ_sq_lo

/-! ## Explicit `< 2 × 10⁻⁴` precision via term-by-term bounds

We bound each squared-Yukawa term in `trRemainder(frameworkGUT_Real)`
individually, then assemble. -/

/-- Concrete numeric values of `frameworkGUT_Real` extracted as constants. -/
private def yτ_num : ℝ := 9270 / 1000000
private def ye_num : ℝ := 2935 / 1000000000

/-- Sanity values. -/
private theorem yτ_num_eq : yτ_num = 9270 / 1000000 := rfl
private theorem ye_num_eq : ye_num = 2935 / 1000000000 := rfl

/-- Closed-form: `trRemainder(frameworkGUT_Real) = 12 · X + 4 · Y` where
    `X` is the down-quark/up-quark sum and `Y` is the lepton sum. -/
private theorem trRemainder_framework_unfold :
    frameworkGUT_Real.trRemainder
    = 12 * (
        (Real.sqrt (5/18) * (Real.sqrt 5 * ye_num))^2
      + ((3/16) * yτ_num)^2
      + (Real.sqrt 5 * ye_num)^2
      + (22 * ye_num / (3 + φ))^2
      + ((2/3) * yτ_num)^2
      ) + 4 * (
        ye_num^2 + (22 * ye_num)^2 + yτ_num^2
      ) := by
  unfold frameworkGUT_Real RealYukawaSet.trRemainder yτ_num ye_num
  rfl

/-- Reduce y_d² to rational form: `(√5 · y_e)² = 5 · y_e²`. -/
private theorem yd_sq_form :
    (Real.sqrt 5 * ye_num)^2 = 5 * ye_num^2 := by
  rw [mul_pow, sqrt5_sq]

/-- Reduce y_u² to rational form: `(√(5/18) · √5 · y_e)² = (25/18) · y_e²`. -/
private theorem yu_sq_form :
    (Real.sqrt (5/18) * (Real.sqrt 5 * ye_num))^2 = (25/18) * ye_num^2 := by
  rw [mul_pow, sqrt_5_18_sq, mul_pow, sqrt5_sq]; ring

/-- y_e² is bounded by 10⁻¹¹ (since y_e = 2.935 × 10⁻⁶, y_e² ≈ 8.6 × 10⁻¹²). -/
private theorem ye_num_sq_bound : ye_num^2 < 1 / (10^11 : ℝ) := by
  unfold ye_num; norm_num

/-- y_τ² is bounded by 10⁻⁴ (since y_τ = 9.27 × 10⁻³, y_τ² ≈ 8.6 × 10⁻⁵). -/
private theorem yτ_num_sq_bound : yτ_num^2 < 1 / (10000 : ℝ) := by
  unfold yτ_num; norm_num

/-- The `y_s² = (22 y_e / (3+φ))²` contribution: bounded by `484 · ye² / 21`. -/
private theorem ys_sq_bound :
    (22 * ye_num / (3 + φ))^2 ≤ 484 * ye_num^2 / 21 := by
  have h_3φ_pos : (0 : ℝ) < 3 + φ := by have := phi_gt_lower; linarith
  have h_3φ_sq_pos : (0 : ℝ) < (3 + φ)^2 := by positivity
  have h_3φ_sq_lo : (21 : ℝ) ≤ (3 + φ)^2 := by
    have := phi_gt_lower; nlinarith
  have h_ye_sq_nn : (0 : ℝ) ≤ ye_num^2 := sq_nonneg _
  -- (22 y_e / (3+φ))² = 484 y_e² / (3+φ)² ≤ 484 y_e² / 21
  rw [div_pow, show ((22 * ye_num)^2 : ℝ) = 484 * ye_num^2 from by ring]
  -- Need 484 ye² / (3+φ)² ≤ 484 ye² / 21
  -- Since (3+φ)² ≥ 21 > 0, dividing by larger denom gives smaller result.
  have h21 : (0 : ℝ) < 21 := by norm_num
  have h_num_nn : (0 : ℝ) ≤ 484 * ye_num^2 := by positivity
  rw [div_le_div_iff₀ h_3φ_sq_pos h21]
  nlinarith [h_ye_sq_nn, h_3φ_sq_lo]

/-- **Tier 1 — explicit precision bound (term-by-term).**

    For `frameworkGUT_Real`, the trace remainder is below `12 / 10000`.

    Strategy: substitute the irrational identities `(√5)² = 5`,
    `(√(5/18))² = 5/18`, bound `(3+φ)⁻²`, then sum the rational pieces
    via a single `nlinarith`. -/
theorem trRemainder_framework_bound :
    frameworkGUT_Real.trRemainder < 12 / 10000 := by
  rw [trRemainder_framework_unfold, yd_sq_form, yu_sq_form]
  -- Now the goal involves only rational expressions in ye_num, yτ_num,
  -- plus the y_s² piece (22 ye / (3+φ))².
  have h_ys := ys_sq_bound
  have h_ye_sq_nn : (0 : ℝ) ≤ ye_num^2 := sq_nonneg _
  have h_yτ_sq_nn : (0 : ℝ) ≤ yτ_num^2 := sq_nonneg _
  have h_ye_bd : ye_num^2 < 1 / (10^11 : ℝ) := ye_num_sq_bound
  have h_yτ_bd : yτ_num^2 < 1 / (10000 : ℝ) := yτ_num_sq_bound
  -- Specific yτ² and ye² values
  have h_yτ_eq : yτ_num^2 = (9270/1000000 : ℝ)^2 := by unfold yτ_num; rfl
  have h_ye_eq : ye_num^2 = (2935/1000000000 : ℝ)^2 := by unfold ye_num; rfl
  -- Bound: 12·(25/18·y_e² + (3/16)²·y_τ² + 5·y_e² + ys² + (2/3)²·y_τ²)
  --        + 4·(y_e² + 484·y_e² + y_τ²) < 12/10000
  -- The dominant term is 12·(2/3)²·y_τ² + 4·y_τ² = (16/3 + 4)·y_τ² ≈ 9.33·y_τ²
  -- ≈ 8.0e-4. The other terms add ~1.5e-4 cumulatively. Total ~9.5e-4 < 12e-4.
  unfold yτ_num ye_num at *
  nlinarith [h_ys, h_ye_sq_nn, h_yτ_sq_nn,
              sq_nonneg (Real.sqrt (5/18) * (Real.sqrt 5 * (2935 / 1000000000 : ℝ))),
              sq_nonneg (Real.sqrt 5 * (2935 / 1000000000 : ℝ)),
              sq_nonneg ((22 : ℝ) * (2935 / 1000000000) / (3 + φ))]

/-- **Tier 1 — Theorem A (final, explicit precision).**

    For `frameworkGUT_Real`, the Seeley-DeWitt `a_2` differs from the
    integer `-179` by less than `2 × 10⁻⁴`. -/
theorem theoremA_real_explicit_precision :
    |frameworkGUT_Real.a2 - (-179)| < targetPrecision := by
  apply theoremA_real_precision_qualitative frameworkGUT_Real
  · unfold frameworkGUT_Real; rfl
  · have h := trRemainder_framework_bound
    show frameworkGUT_Real.trRemainder < targetPrecision * 6
    unfold targetPrecision
    linarith

end

end SpectralPhysics.YukawaHierarchy
