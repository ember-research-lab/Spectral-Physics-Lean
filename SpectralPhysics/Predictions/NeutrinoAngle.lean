/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Predictions.CabibboAngle

/-!
# The Reactor Neutrino Angle from Cabibbo Mixing

θ₁₃ = λ/√2 ≈ 0.1584 (as sin θ₁₃)

Measured: sin(θ₁₃) = 0.150 ± 0.01. Agreement: 6%.

## References

* Ben-Shalom, "Spectral Physics", Theorem 40.5
-/

noncomputable section

open Real

/-- The reactor neutrino mixing parameter: sin(θ₁₃) = λ/√2 -/
def neutrinoAngle : ℝ := cabibboParam / Real.sqrt 2

/-- Closed form: (150 - 23√5) / (440√2) -/
theorem neutrinoAngle_closed_form :
    neutrinoAngle = (150 - 23 * Real.sqrt 5) / (440 * Real.sqrt 2) := by
  simp only [neutrinoAngle]
  rw [cabibbo_closed_form]
  field_simp

/-- Numerical value ≈ 0.1584 -/
theorem neutrinoAngle_approx :
    |neutrinoAngle - 0.1584| < 0.002 := by
  simp only [neutrinoAngle]
  have h_cab := cabibbo_approx -- |cabibboParam - 0.2240| < 0.001
  rw [abs_lt] at h_cab
  have h2_lo : (1.414 : ℝ) < Real.sqrt 2 := by
    rw [show (1.414 : ℝ) = Real.sqrt (1.414 ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.414)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h2_hi : Real.sqrt 2 < (1.415 : ℝ) := by
    rw [show (1.415 : ℝ) = Real.sqrt (1.415 ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.415)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h2_pos : (0 : ℝ) < Real.sqrt 2 := by linarith
  -- cabibboParam / √2 ∈ ((0.2240-0.001)/1.415, (0.2240+0.001)/1.414)
  --                     ≈ (0.1576, 0.1590)
  -- |... - 0.1584| < max(0.0008, 0.0006) < 0.002 ✓
  have hlo : 0.1584 - 0.002 < cabibboParam / Real.sqrt 2 := by
    rw [lt_div_iff₀ h2_pos]; nlinarith [h_cab.1]
  have hhi : cabibboParam / Real.sqrt 2 < 0.1584 + 0.002 := by
    rw [div_lt_iff₀ h2_pos]; nlinarith [h_cab.2]
  exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩

/-- Agreement with experiment: 6% -/
theorem neutrinoAngle_agreement :
    let predicted := neutrinoAngle
    let measured := (0.150 : ℝ)
    |predicted - measured| / measured < 0.07 := by
  simp only
  have h := neutrinoAngle_approx
  rw [abs_lt] at h
  rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 0.150)]
  rw [abs_lt]
  constructor <;> nlinarith [h.1, h.2]

end
