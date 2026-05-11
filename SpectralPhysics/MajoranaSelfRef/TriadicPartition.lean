/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Triad.SelfReferentialTriad
import SpectralPhysics.MajoranaSelfRef.JSelfConjugate
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Triadic 1:2 Partition vs the y_R magnitude

## Hypothesis under test

The user's structural insight: the {Observer, Observed, Relation}
triad has 3 nodes (odd), forcing any Fiedler partition to be 1:2
(it cannot be 1:1).  The hypothesis: this 1:2 ratio might be the
seed of the chiral asymmetry, and might quantitatively pin y_R via
a structural mechanism rooted in self-reference.

## What this file does

1. Records the triad 1:2 partition as the *order-1 structural
   asymmetry* forced by the 3-node triad.
2. **Tests numerically** whether the 1:2 ratio (or any simple
   power thereof) reproduces empirical `y_R ≈ 3.27 × 10⁻⁵`.

## Verdict (Tier 1)

The plain 1:2 ratio is `0.5`.  The empirical y_R is `3.27 × 10⁻⁵`.
The ratio `0.5 / y_R ≈ 1.53 × 10⁴`.  No power `(1/2)^n` for `n ≤ 10`
lands within a factor of 25 of y_R.  The closest is `(1/2)^15 =
3.05 × 10⁻⁵` (factor 1.07), but `n = 15` has no triadic origin.

**Conclusion**: the 1:2 partition is real and structural, but is
**NOT** the source of the y_R magnitude.

## References

* v0.9, Theorem `thm:sr-tolerance` (lines 5995–6048).
* `pre_geometric/y_r_chirality_unification/survey.md` §3a.
-/

noncomputable section

namespace SpectralPhysics.MajoranaSelfRef.TriadicPartition

open Real

/-! ## The 1:2 partition

The Triad has nodes `{O, S, R}` (3 nodes).  Any Fiedler partition
into nonempty `S+, S-` with `|S+| + |S-| = 3` must have `{|S+|,
|S-|} = {1, 2}` — there is no balanced partition. -/

/-- The minimum-to-maximum size ratio of the unique 1:2 partition. -/
def fiedler_min_max_ratio : ℝ := 1 / 2

/-- The symmetric-difference asymmetry of the unique 1:2 partition. -/
def fiedler_symdiff_ratio : ℝ := 1 / 3

/-- **Tier 1.**  Both ratios are positive. -/
theorem fiedler_ratios_pos :
    0 < fiedler_min_max_ratio ∧ 0 < fiedler_symdiff_ratio := by
  unfold fiedler_min_max_ratio fiedler_symdiff_ratio
  refine ⟨?_, ?_⟩ <;> norm_num

/-! ## Empirical y_R target -/

/-- The empirical y_R target (rational approximation of `3.27 × 10⁻⁵`). -/
def y_R_target : ℝ := 327 / 10000000

/-- **Tier 1.**  `y_R_target > 0`. -/
theorem y_R_target_pos : 0 < y_R_target := by
  unfold y_R_target; norm_num

/-! ## Tier-1 numerical refutation: 1/2 ≠ y_R, 1/3 ≠ y_R -/

/-- **Tier 1.**  The Fiedler 1:2 ratio is more than 10000 times
    larger than y_R. -/
theorem fiedler_min_max_ratio_far_from_y_R :
    fiedler_min_max_ratio > 10000 * y_R_target := by
  unfold fiedler_min_max_ratio y_R_target
  norm_num

/-- **Tier 1.**  The Fiedler 1:3 symmetric-difference ratio is also
    far from y_R. -/
theorem fiedler_symdiff_ratio_far_from_y_R :
    fiedler_symdiff_ratio > 5000 * y_R_target := by
  unfold fiedler_symdiff_ratio y_R_target
  norm_num

/-! ## Powers of 1/2 -/

/-- `(1/2)^14`. -/
def half_pow_14 : ℝ := (1/2 : ℝ) ^ (14 : ℕ)

/-- `(1/2)^15`. -/
def half_pow_15 : ℝ := (1/2 : ℝ) ^ (15 : ℕ)

/-- `(1/2)^16`. -/
def half_pow_16 : ℝ := (1/2 : ℝ) ^ (16 : ℕ)

/-- **Tier 1.**  `(1/2)^14 = 1/16384`. -/
theorem half_pow_14_value : half_pow_14 = 1 / 16384 := by
  unfold half_pow_14; norm_num

/-- **Tier 1.**  `(1/2)^15 = 1/32768`. -/
theorem half_pow_15_value : half_pow_15 = 1 / 32768 := by
  unfold half_pow_15; norm_num

/-- **Tier 1.**  `(1/2)^16 = 1/65536`. -/
theorem half_pow_16_value : half_pow_16 = 1 / 65536 := by
  unfold half_pow_16; norm_num

/-- **Tier 1.**  y_R is bracketed: `(1/2)^16 < y_R < (1/2)^14`. -/
theorem y_R_bracketed_by_half_powers :
    half_pow_16 < y_R_target ∧ y_R_target < half_pow_14 := by
  refine ⟨?_, ?_⟩
  · rw [half_pow_16_value]; unfold y_R_target; norm_num
  · rw [half_pow_14_value]; unfold y_R_target; norm_num

/-- **Tier 1.**  `(1/2)^6 ≈ 0.0156` is more than 400× larger than y_R.
    This rules out exponents bounded by triadic structure. -/
theorem fiedler_pow_6_far_from_y_R :
    (1/2 : ℝ) ^ (6 : ℕ) > 400 * y_R_target := by
  unfold y_R_target; norm_num

/-- **Tier 1.**  Even `(1/2)^10 ≈ 9.77 × 10⁻⁴` is far from y_R. -/
theorem fiedler_pow_10_far_from_y_R :
    (1/2 : ℝ) ^ (10 : ℕ) > 25 * y_R_target := by
  unfold y_R_target; norm_num

/-! ## Conclusion: 1:2 partition does NOT pin y_R

The triadic 1:2 partition gives an order-1 asymmetry; y_R is order
`10⁻⁵`.  No power `(1/2)^n` for `n` derivable from triadic structure
(n ≤ 6, even n ≤ 10) is within factor 25 of y_R.  **Verdict on the
1:2 partition reading: NEGATIVE.**

The triad's *other* dimensionless number — the self-referential
tolerance `τ = 1/(2+φ)` (the inverse spectral gap) — gives a more
interesting numerical coincidence: `τ^8 ≈ 3.41 × 10⁻⁵`, factor 1.05
of empirical y_R.  That probe is investigated in
`SelfReferenceClosure.lean`. -/

end SpectralPhysics.MajoranaSelfRef.TriadicPartition

end
