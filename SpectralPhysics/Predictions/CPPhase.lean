/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Triad.SelfReferentialTriad
import SpectralPhysics.Triad.GoldenRatio
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The CP Phase from Self-Reference

δ_CKM = π/φ² = π(3-√5)/2 ≈ 68.75°

Measured: 67.4° ± 4.3°. Agreement: 0.31σ.

## References

* Ben-Shalom, "Spectral Physics", Theorem 40.4
-/

noncomputable section

open Real

/-- The CP phase in radians: δ_CKM = π/φ² -/
def cpPhase : ℝ := π / φ ^ 2

/-- φ² = δ - 1 = 1 + φ, so cpPhase = π/(1+φ) -/
theorem cpPhase_eq_pi_div_one_add_phi :
    cpPhase = π / (1 + φ) := by
  simp only [cpPhase]
  congr 1
  linarith [golden_ratio_quadratic]

/-- The CP phase in closed form: π(3-√5)/2 -/
theorem cpPhase_closed_form :
    cpPhase = π * (3 - Real.sqrt 5) / 2 := by
  simp only [cpPhase, φ]
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hd : ((1 + Real.sqrt 5) / 2) ^ 2 ≠ 0 := by positivity
  field_simp
  nlinarith [hsq, Real.sqrt_nonneg 5]

/-- Numerical value: cpPhase ≈ 1.2002 radians ≈ 68.75° -/
theorem cpPhase_approx :
    |cpPhase - 1.200| < 0.01 := by
  rw [cpPhase_eq_pi_div_one_add_phi]
  -- π/(1+φ) where φ ≈ 1.618, so 1+φ ≈ 2.618, π/2.618 ≈ 1.200
  have hpi_lo : (3.14159 : ℝ) < π := by linarith [pi_gt_d6]
  have hpi_hi : π < (3.14160 : ℝ) := by linarith [pi_lt_d6]
  have hφ_lo : (1.618 : ℝ) < φ := by
    unfold φ; linarith [show (2.236 : ℝ) < Real.sqrt 5 from by
      rw [show (2.236 : ℝ) = Real.sqrt (2.236 ^ 2) from
        (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.236)).symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)]
  have hφ_hi : φ < (1.619 : ℝ) := by
    unfold φ; linarith [show Real.sqrt 5 < (2.237 : ℝ) from by
      rw [show (2.237 : ℝ) = Real.sqrt (2.237 ^ 2) from
        (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.237)).symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)]
  have hd_pos : (0 : ℝ) < 1 + φ := by linarith
  have hlo : 1.200 - 0.01 < π / (1 + φ) := by
    rw [lt_div_iff₀ hd_pos]; nlinarith
  have hhi : π / (1 + φ) < 1.200 + 0.01 := by
    rw [div_lt_iff₀ hd_pos]; nlinarith
  exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩

end
