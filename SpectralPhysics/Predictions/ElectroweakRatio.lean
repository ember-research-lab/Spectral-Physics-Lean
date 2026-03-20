/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Triad.SelfReferentialTriad

/-!
# The Electroweak Scale Ratio from Triad Structure

T_c/v = √(3/(2(2+φ))) ≈ 0.6439

Lattice measurement: 0.6478 ± 0.006. Agreement: 0.6%.

## Derivation

1. Critical condition from I* crossing: T_c² = E_gap² / δ
2. Mode counting: v² = (2/3) · E_gap² (2 of 3 triad modes condense)
3. Combining: T_c/v = √(3/(2δ))

No free parameters. The factor 2/3 counts the nonzero eigenvalues of
the triad {0, δ, δ}. The constant δ = 2+φ is the universal self-referential
scale parameter.

## References

* Ben-Shalom, "Spectral Physics", Theorem 25.4
-/

noncomputable section

open Real

/-- The electroweak scale ratio -/
def ewRatio : ℝ := Real.sqrt (3 / (2 * δ))

/-- Expanded form -/
theorem ewRatio_expanded :
    ewRatio = Real.sqrt (3 / (2 * (2 + φ))) := by
  simp [ewRatio, δ]

/-- The ratio satisfies v² = (2δ/3) · T_c² -/
theorem vev_crossover_relation :
    ewRatio ^ 2 = 3 / (2 * δ) := by
  simp only [ewRatio]
  have hδ_pos : (0 : ℝ) < δ := by simp [δ]; unfold φ; positivity
  rw [Real.sq_sqrt (div_nonneg (by norm_num) (by linarith))]

/-- Numerical approximation -/
theorem ewRatio_approx :
    |ewRatio - 0.6439| < 0.001 := by
  -- ewRatio = √(3/(2(2+φ))). Bound the argument, then bound the sqrt.
  have h5_lo : (2.236 : ℝ) < Real.sqrt 5 := by
    rw [show (2.236 : ℝ) = Real.sqrt (2.236 ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.236)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h5_hi : Real.sqrt 5 < (2.237 : ℝ) := by
    rw [show (2.237 : ℝ) = Real.sqrt (2.237 ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.237)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hφ_lo : (1.618 : ℝ) < φ := by unfold φ; linarith
  have hφ_hi : φ < (1.619 : ℝ) := by unfold φ; linarith
  -- 3/(2(2+φ)) ∈ (3/7.238, 3/7.236) ≈ (0.41448, 0.41459)
  -- √0.41448 ≈ 0.64380, √0.41459 ≈ 0.64388
  -- We need |√x - 0.6439| < 0.001, i.e., 0.6429 < √x < 0.6449
  -- 0.6429² = 0.41332, 0.6449² = 0.41590
  -- Our x ∈ (0.41448, 0.41459), within (0.41332, 0.41590) ✓
  have hv := vev_crossover_relation -- ewRatio ^ 2 = 3 / (2 * δ)
  have hew_pos : 0 ≤ ewRatio := by simp [ewRatio]; positivity
  -- Bound δ = 2 + φ using φ bounds
  have hδ_lo : (3.618 : ℝ) < δ := by simp [δ]; linarith [hφ_lo]
  have hδ_hi : δ < (3.619 : ℝ) := by simp [δ]; linarith [hφ_hi]
  -- Bound ewRatio² = 3/(2δ) using φ bounds
  -- δ ∈ (3.618, 3.619), so 3/(2δ) ∈ (3/7.238, 3/7.236) ≈ (0.41448, 0.41459)
  -- Since 0.643² = 0.413449 < 0.41448 and 0.645² = 0.416025 > 0.41459:
  --   0.643 < ewRatio < 0.645, so |ewRatio - 0.6439| < 0.002 < 0.001? No, need tighter.
  -- Actually 0.6435² = 0.414094 < 0.41448 and 0.6445² = 0.415380 > 0.41459
  --   0.6435 < ewRatio < 0.6445, |ewRatio - 0.6439| < 0.0006 < 0.001 ✓
  have hδ_pos : (0 : ℝ) < 2 * δ := by nlinarith [hδ_lo]
  -- Lower bound on ewRatio via sq_nonneg
  have hsq_lo : (0.4144 : ℝ) < ewRatio ^ 2 := by
    rw [hv]; rw [lt_div_iff₀ hδ_pos]; nlinarith [hδ_hi]
  have hew_lo : (0.6435 : ℝ) < ewRatio := by nlinarith [sq_nonneg (ewRatio - 0.6435)]
  -- Upper bound on ewRatio via sq_nonneg
  have hsq_hi : ewRatio ^ 2 < (0.4146 : ℝ) := by
    rw [hv]; rw [div_lt_iff₀ hδ_pos]; nlinarith [hδ_lo]
  have hew_hi : ewRatio < (0.6445 : ℝ) := by nlinarith [sq_nonneg (ewRatio - 0.6445)]
  -- ewRatio ∈ (0.6435, 0.6445), |ewRatio - 0.6439| < 0.0006 < 0.001
  rw [abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- Agreement with lattice QCD: 0.6% -/
theorem ewRatio_agreement :
    let predicted := ewRatio
    let measured := (0.6478 : ℝ)
    |predicted - measured| / measured < 0.01 := by
  simp only
  -- Use ewRatio_approx: |ewRatio - 0.6439| < 0.001
  -- So ewRatio ∈ (0.6429, 0.6449)
  -- |ewRatio - 0.6478| ∈ (0.0029, 0.0049)
  -- |ewRatio - 0.6478| / 0.6478 < 0.0049/0.6478 ≈ 0.0076 < 0.01 ✓
  have h := ewRatio_approx
  rw [abs_lt] at h
  rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 0.6478)]
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]

end
