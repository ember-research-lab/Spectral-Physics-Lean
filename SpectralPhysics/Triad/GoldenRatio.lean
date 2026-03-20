/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Real.Sqrt
import SpectralPhysics.Triad.SelfReferentialTriad

/-!
# Golden Ratio Properties for Spectral Physics

The golden ratio φ = (1+√5)/2 appears throughout the framework as the
unique fixed point of the self-referential equation w = 1 + 1/w.

This file collects the arithmetic identities involving φ that are needed
for the derived predictions. Mathlib has `goldenRatio` defined; we bridge
to our notation and prove the specific identities the framework uses.
-/

noncomputable section

open Real

-- Mathlib defines `goldenRatio : ℝ` as `(1 + √5) / 2`
-- We use φ as our notation (defined in SelfReferentialTriad.lean)

/-- Bridge to Mathlib's golden ratio -/
theorem phi_eq_goldenRatio : φ = goldenRatio := by
  simp [φ, goldenRatio]

/-- φ > 1 -/
theorem phi_gt_one : φ > 1 := by
  have h5 : Real.sqrt 5 > 1 := by
    rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  unfold φ; linarith

/-- φ > 0 -/
theorem phi_pos : φ > 0 := by
  linarith [phi_gt_one]

/-- 2 + φ > 0 (needed for τ = 1/(2+φ)) -/
theorem two_add_phi_pos : (2 : ℝ) + φ > 0 := by
  linarith [phi_pos]

/-- φ · (φ - 1) = 1 (the "spectral self-consistency" identity) -/
theorem phi_mul_phi_sub_one : φ * (φ - 1) = 1 := by
  have h := golden_ratio_quadratic -- φ ^ 2 = φ + 1
  nlinarith [h, sq φ]

/-- 1/φ = φ - 1 -/
theorem inv_phi : 1 / φ = φ - 1 := by
  rw [div_eq_iff (ne_of_gt phi_pos)]
  linarith [phi_mul_phi_sub_one]

/-- φ + 1/φ = √5 -/
theorem phi_add_inv_phi : φ + 1 / φ = Real.sqrt 5 := by
  rw [inv_phi]  -- 1/φ = φ - 1
  -- Goal: φ + (φ - 1) = √5, i.e., 2φ - 1 = √5
  unfold φ; field_simp; ring

/-- (2+φ)² = 5 + 5φ = 5φ² -/
theorem delta_sq : (2 + φ)^2 = 5 + 5 * φ := by
  have h := golden_ratio_quadratic -- φ ^ 2 = φ + 1
  nlinarith [h, sq φ]

-- Key identity for the Cabibbo derivation:
-- τ² = τ(1 - 2τ + τ) ... actually let's just collect what we need.

/-- τ in terms of φ: τ = 1/(2+φ) = (3-φ)/5 -/
theorem tau_alt_form : τ = (3 - φ) / 5 := by
  simp only [τ]
  have hd : (2 : ℝ) + φ ≠ 0 := by
    have : φ > 0 := phi_pos
    linarith
  rw [div_eq_div_iff hd (by norm_num : (5:ℝ) ≠ 0)]
  -- Goal: 1 * 5 = (3 - φ) * (2 + φ)
  have h := golden_ratio_quadratic
  nlinarith [h, sq φ]

/-- (3-φ) = √5/φ (a useful identity) -/
theorem three_sub_phi : 3 - φ = Real.sqrt 5 / φ := by
  have hne : φ ≠ 0 := ne_of_gt phi_pos
  rw [eq_div_iff hne]
  -- Goal: (3 - φ) * φ = √5
  simp only [φ]
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  field_simp
  nlinarith [hsq, Real.sqrt_nonneg 5]

end
