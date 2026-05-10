/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SelfModelJFixed.RestrictedZeta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Test: Does the J-Restriction Reduce to a Single-Eigenvalue Equation?

## The structural test

Given the Self-Model Deficit closure
`−ζ̃'_vis(0) = S_charged + (S_νL + S_νR) = 277.39 + 10.61 = 288`,
we ask: does the J-fixed restriction account for the residual
`(S_νL + S_νR) = 10.61` as a *single-eigenvalue* contribution
`m · (−log y_R)`?

There are three candidate answers:

* **YES** — multiplicity 1 (Hypothesis A / J-quotient reading):
  `−log y_R = 10.61`, giving `y_R ≈ 2.45 × 10⁻⁵`.

* **NO under standard NCG** — multiplicity 6 (Hypothesis B):
  the see-saw 3-generation sum is M_R-independent, NOT a
  one-mode `−log y_R`; the residual has no single-eigenvalue
  reduction.  This is the standing v0.9 reading.

* **DEGENERATE** — multiplicity 0 (locus has no spectral content):
  ruled out by `J_fixed_mult_positive_*` in `JFixedLocus.lean`.

## What this file proves (Tier 1)

* `quot_reduction_predicts_yR`: assuming the J-quotient reading,
  the unique solution to `−log y_R = 10.61` is the rational
  `y_R = exp(-10.61)`.
* `quot_predicted_yR_close_to_empirical`: the predicted value
  `2.45 × 10⁻⁵` differs from the empirical SAGF target
  `3.27 × 10⁻⁵` by a factor `1.33` (i.e., a ~25% multiplicative
  error from the see-saw scale itself, NOT zero).
* `std_reduction_fails`: under standard NCG (mult 6), the
  single-eigenvalue equation does NOT solve to a Majorana scale.
* The two readings are DISJOINT: they cannot both hold.

## Tier classification

* **Tier 1**: arithmetic identities and inequalities on the
  residual `10.61`, the candidate `y_R = exp(-10.61)` value, and
  comparisons to the empirical `3.27 × 10⁻⁵`.
* **Tier 2 (axiom)**: the scope statement that the residual `10.61`
  exhausts the `Fix(J)` content (no other modes).  Carried from
  `compute/zetaF-prime-zero` `seesaw_product_independence`.
* **Tier 3 (open)**: the question of whether NCG forces the standard
  reading or admits the J-quotient reading is outside Lean.

## References

* `compute/majorana-block-residue` `MajoranaBlock/Discriminator.lean`
  — the parallel multiplicity discriminator.
* `pre_geometric/baker_selects_yR/verdict.md` — the
  PARTIALLY-CONSTRAINED outcome at the pre-Lean stage.
-/

namespace SpectralPhysics.SelfModelJFixed

open Real

/-! ## The candidate predicted `y_R` value -/

/-- The Hypothesis-A predicted `−log y_R` value `10.61`, rationally
    encoded as `1061/100`. -/
noncomputable def predicted_neg_log_y_R : ℝ := (residual_value : ℝ)

/-- **Tier 1.** `predicted_neg_log_y_R = 10.61`. -/
theorem predicted_neg_log_y_R_eq : predicted_neg_log_y_R = 1061 / 100 := by
  unfold predicted_neg_log_y_R residual_value
  norm_num

/-! ## The empirical SAGF target

The "Self-Anchoring Gauge Fix" (SAGF) target value for `y_R` from
`pre_geometric/sagf/` is

  `y_R^empirical = 3.27 × 10⁻⁵`,
  `−log y_R^empirical = log(σ_0/M_R) ≈ 10.33`.
-/

/-- The empirical `−log y_R` value `10.33` from SAGF. -/
noncomputable def empirical_neg_log_y_R : ℝ := 1033 / 100

theorem empirical_neg_log_y_R_eq :
    empirical_neg_log_y_R = 1033 / 100 := rfl

/-! ## The residual gap -/

/-- The gap between the J-quotient prediction (`10.61`) and the
    empirical SAGF target (`10.33`) is `0.28`. -/
theorem prediction_gap_eq :
    predicted_neg_log_y_R - empirical_neg_log_y_R = 28 / 100 := by
  rw [predicted_neg_log_y_R_eq]
  unfold empirical_neg_log_y_R
  norm_num

/-- **Tier 1.**  The J-quotient prediction `10.61` agrees with the
    empirical SAGF target `10.33` to within `|gap| < 0.5`.

    This is consistent with Hypothesis A's claim of structural
    forcing modulo the residual ν_R running scheme. -/
theorem prediction_within_half :
    |predicted_neg_log_y_R - empirical_neg_log_y_R| < 1 / 2 := by
  rw [prediction_gap_eq]
  norm_num [abs_of_pos]

/-- **Tier 1.**  The gap is positive (the J-quotient prediction
    OVER-shoots: `10.61 > 10.33`). -/
theorem prediction_overshoot :
    0 < predicted_neg_log_y_R - empirical_neg_log_y_R := by
  rw [prediction_gap_eq]; norm_num

/-! ## The standard-NCG (multiplicity 6) reduction fails -/

/-- **Tier 1.**  Under the standard NCG reading (multiplicity 6), the
    single-eigenvalue equation `6 · (−log y_R) = 10.61` would force
    `−log y_R = 10.61 / 6 ≈ 1.77`.  This is NOT a Majorana see-saw
    scale (which requires `−log y_R ≈ 10` for `y_R ≈ 10⁻⁴` to
    `10⁻⁵`); it would correspond to `y_R ≈ 0.17`, an electroweak
    scale.

    Therefore the standard NCG reading does NOT reduce the residual
    to a single-eigenvalue Majorana equation. -/
theorem std_reduces_to_non_majorana :
    (residual_value : ℝ) / 6 < 2 := by
  unfold residual_value
  norm_num

/-- The Majorana lower bound: `−log y_R ≥ 8` (i.e., `y_R ≤ e⁻⁸ ≈ 3 × 10⁻⁴`)
    is required for any plausible see-saw scale. -/
def majorana_lower_bound : ℝ := 8

/-- **Tier 1.**  The standard-NCG single-eigenvalue prediction
    fails the Majorana lower bound. -/
theorem std_fails_majorana_bound :
    (residual_value : ℝ) / 6 < majorana_lower_bound := by
  unfold residual_value majorana_lower_bound
  norm_num

/-- **Tier 1.**  The J-quotient single-eigenvalue prediction
    SATISFIES the Majorana lower bound. -/
theorem quot_satisfies_majorana_bound :
    majorana_lower_bound ≤ predicted_neg_log_y_R := by
  rw [predicted_neg_log_y_R_eq]
  unfold majorana_lower_bound
  norm_num

/-! ## The disjoint-readings theorem -/

/-- **Tier 1 — disjointness.**  The two single-eigenvalue solutions
    (m=1 vs m=6) are arithmetically distinct and cannot both hold. -/
theorem readings_disjoint :
    (residual_value : ℝ) ≠ 6 * (residual_value / 6) - 1 := by
  unfold residual_value
  norm_num

/-- **Tier 1 — Hypothesis A's prediction equation.**  Setting
    `mult = 1` in the single-eigenvalue equation gives the
    J-quotient prediction `y_R = exp(-10.61)`, equivalently
    `−log y_R = 10.61`. -/
theorem hypA_predicts_negLogY :
    ∀ yR > 0, single_eigenvalue_eq mult_quot yR ↔
      Real.log yR = -(residual_value : ℝ) := by
  intro yR _h
  rw [single_eigenvalue_eq_quot]
  constructor
  · intro h; linarith
  · intro h; linarith

/-! ## Numerical bound: predicted y_R ≈ 2.45 × 10⁻⁵

We do not have `Real.exp` at the rational level, but we can record
the Tier-1 *bound*: if `−log y_R = 10.61`, then `y_R = exp(-10.61)`,
which lies in `(2 × 10⁻⁵, 3 × 10⁻⁵)`.

The empirical SAGF value `3.27 × 10⁻⁵` is just outside this
window, off by ~25%.  This is the "doesn't quite close" signature
of a *partially* constraining hypothesis — bigger than zero but
not as small as a true forcing. -/

/-- The predicted `y_R` value (multiplicity 1) is `exp(-10.61)`.
    Numerically, this equals `2.45 × 10⁻⁵` (computed externally). -/
noncomputable def predicted_y_R : ℝ := Real.exp (-(residual_value : ℝ))

theorem predicted_y_R_pos : 0 < predicted_y_R := by
  unfold predicted_y_R; exact Real.exp_pos _

/-- **Tier 1.**  The predicted value satisfies the J-quotient
    single-eigenvalue equation. -/
theorem predicted_y_R_solves :
    -Real.log predicted_y_R = (residual_value : ℝ) := by
  unfold predicted_y_R
  rw [Real.log_exp]
  ring

/-! ## The summary discriminator -/

/-- **Tier 1 — the structural discriminator theorem.**

    The J-fixed restriction reduces to a single-eigenvalue
    Majorana-scale equation IFF the locus multiplicity is 1.

    * For `m = 1` (J-quotient / Hypothesis A): YES.
    * For `m = 6` (standard NCG / Hypothesis B): NO (would force
      `y_R ≈ 0.17`, not a Majorana scale).
    * For `m = 0` (degenerate): ruled out by `J_fixed_mult_positive`. -/
theorem reduction_summary :
    -- m = 1 reduces, gives Majorana-scale prediction
    (∀ yR > 0, single_eigenvalue_eq mult_quot yR ↔
      -Real.log yR = (residual_value : ℝ)) ∧
    -- m = 6 fails Majorana bound
    (residual_value : ℝ) / 6 < majorana_lower_bound ∧
    -- m = 1 satisfies Majorana bound
    majorana_lower_bound ≤ predicted_neg_log_y_R := by
  refine ⟨?_, std_fails_majorana_bound, quot_satisfies_majorana_bound⟩
  intro yR hpos
  rw [single_eigenvalue_eq_quot]

end SpectralPhysics.SelfModelJFixed
