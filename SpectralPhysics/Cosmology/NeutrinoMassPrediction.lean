/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import SpectralPhysics.SelfModelDeficit.Kappa2
import SpectralPhysics.SelfModelDeficit.F4Coefficient

/-!
# Neutrino mass prediction from CC closure

The framework's CC closure (via `Kappa2.lean` + `F4Coefficient.lean`) reduces
to a **single open parameter**: the see-saw scale ξ_R. Manuscript v0.9.2
Remark `rem:m1-sensitivity` (line 7978) states that ξ_R is determined by
the lightest neutrino mass m_1 via the functional-determinant constraint
on Σm_D² (sum of squared Dirac neutrino masses, line 7975).

## Two routes (NOT fully independent — see caveat)

* **Route 1 (manuscript line 7985)**: Functional-determinant constraint
  −ζ'_vis(0) = 288 fixes the Dirac neutrino product. Combined with NH
  oscillation data, predicts Σm_ν ∈ [0.058, 0.063] eV.

* **Route 2 (CC closure, this file)**: Λ_obs → κ₂ = 529.42 (Lean theorem
  in `Kappa2.lean`) → ξ_R = 3.7090 → M_R = Λ_c·exp(-ξ_R) ≈ 4.78×10¹⁴ GeV.
  Combined with manuscript anchors (line 7979), predicts Σm_ν ≈ 0.061 eV.

> ⚠️ **CAVEAT (2026-05-26 rigor audit).** Route 2 is **NOT independent** of the
> CC target. Its `ξ_R = 3.7090` is the bisection root tuned so that
> `κ₂ = 529.42` matches `2·ln(Λ_c²/Λ_obs)` (admitted in `Kappa2.lean` docstring
> line 49: this is the "Baker target κ₂_needed_obs"). So Route 2 runs
> **Λ_obs → κ₂ → ξ_R → Σm_ν** — it is a *consistency check* on the CC tuning,
> not an independent corroboration. The genuinely independent prediction is
> **Route 1 (functional determinant) + the NH kinematic floor** proved in
> `Predictions/NeutrinoMass.lean` (`sigmaMnu_floor`, real √-analysis from
> measured Δm²). The theorems below (`CC_closure_in_prediction_range`,
> `two_route_consistency`) are T1 arithmetic **on quoted constants** — they
> verify the consistency/falsifiability framing, not the see-saw derivation
> (which the manuscript flags OPEN: "Σmν/CC closure as a single Lean theorem").
> See `results/CHAIN-RIGOR-LEDGER.md`.

This file connects the two routes via the ξ_R see-saw scale and locks the
prediction in the manuscript's stated range.

## References

* Ben-Shalom, "Spectral Physics", v0.9.2, Remark `rem:m1-sensitivity`
  (line 7978), Section `sec:cc-constraint` (line 7838), Prediction
  `pred:neutrino-mass` (line 8218).
* `pre_geometric/Lambda1_refined/scse_refined.py` (ξ_R bisection).
-/

namespace SpectralPhysics.Cosmology

open Real
open SpectralPhysics.SelfModelDeficit

/-! ## See-saw scale from CC closure -/

/-- The CC-closure see-saw scale, bisected from κ₂ = 529.42 target.
    Source: `pre_geometric/Lambda1_refined/scse_refined.py`. -/
noncomputable def xi_R_CC : ℝ := 37090 / 10000   -- 3.7090

theorem xi_R_CC_pos : 0 < xi_R_CC := by
  unfold xi_R_CC; norm_num

/-! ## Predicted M_R via the inverse of ξ_R = log(Λ_c/M_R) -/

/-- M_R predicted from ξ_R = log(Λ_c/M_R), parameterised by Λ_c
    (framework value Λ_c = v·e³² ≈ 1.94×10¹⁶ GeV).

    `M_R_predicted Λ_c = Λ_c · exp(-ξ_R_CC)`. -/
noncomputable def M_R_predicted (Lambda_c : ℝ) : ℝ := Lambda_c * exp (-xi_R_CC)

theorem M_R_predicted_pos (Lambda_c : ℝ) (h : 0 < Lambda_c) :
    0 < M_R_predicted Lambda_c := by
  unfold M_R_predicted
  exact mul_pos h (exp_pos _)

/-! ## Manuscript anchors (Remark `rem:m1-sensitivity`, line 7979) -/

/-- Lower anchor: m_1 = 10⁻⁴ eV ↔ M_R = 1.5×10¹⁵ GeV. -/
noncomputable def m1_anchor_lo_eV : ℝ := 1 / 10000          -- 1e-4
noncomputable def MR_anchor_lo_GeV : ℝ := 15 * 10^14         -- 1.5e15

/-- Upper anchor: m_1 = 10⁻² eV ↔ M_R = 2.8×10¹⁴ GeV. -/
noncomputable def m1_anchor_hi_eV : ℝ := 1 / 100            -- 1e-2
noncomputable def MR_anchor_hi_GeV : ℝ := 28 * 10^13         -- 2.8e14

/-! ## Manuscript prediction range (line 7985) -/

/-- Σm_ν lower bound from the framework prediction (NH minimal value). -/
noncomputable def sigma_m_nu_lower_eV : ℝ := 58 / 1000      -- 0.058

/-- Σm_ν upper bound from the framework prediction. -/
noncomputable def sigma_m_nu_upper_eV : ℝ := 63 / 1000      -- 0.063

/-- Falsification threshold (line 16686): Σm_ν > 0.07 with confirmed NH
    refutes the framework prediction. -/
noncomputable def sigma_m_nu_falsify_threshold_eV : ℝ := 7 / 100   -- 0.07

/-! ## Observational compatibility bounds -/

/-- PDG 2024 cosmological bound on Σm_ν. -/
noncomputable def PDG_Sigma_m_nu_bound_eV : ℝ := 12 / 100        -- 0.12

/-- CMB-S4 future 1σ sensitivity. -/
noncomputable def CMB_S4_sensitivity_eV : ℝ := 4 / 100           -- 0.04

/-! ## Observational consistency theorems -/

/-- The framework prediction is BELOW the PDG cosmological bound. -/
theorem sigma_m_nu_upper_lt_PDG :
    sigma_m_nu_upper_eV < PDG_Sigma_m_nu_bound_eV := by
  unfold sigma_m_nu_upper_eV PDG_Sigma_m_nu_bound_eV
  norm_num

/-- The framework prediction is BELOW the falsification threshold. -/
theorem sigma_m_nu_upper_lt_falsify :
    sigma_m_nu_upper_eV < sigma_m_nu_falsify_threshold_eV := by
  unfold sigma_m_nu_upper_eV sigma_m_nu_falsify_threshold_eV
  norm_num

/-- The framework prediction is ABOVE the CMB-S4 sensitivity floor,
    making it detectable by future experiments. -/
theorem sigma_m_nu_lower_gt_CMB_S4 :
    CMB_S4_sensitivity_eV < sigma_m_nu_lower_eV := by
  unfold CMB_S4_sensitivity_eV sigma_m_nu_lower_eV
  norm_num

/-- The prediction range is non-degenerate (lower < upper). -/
theorem sigma_m_nu_range_non_degenerate :
    sigma_m_nu_lower_eV < sigma_m_nu_upper_eV := by
  unfold sigma_m_nu_lower_eV sigma_m_nu_upper_eV
  norm_num

/-- The prediction range width is ~9% of the central value. -/
theorem sigma_m_nu_range_width :
    sigma_m_nu_upper_eV - sigma_m_nu_lower_eV = 5 / 1000 := by
  unfold sigma_m_nu_lower_eV sigma_m_nu_upper_eV
  norm_num

/-! ## CC-closure value (Route 2)

The CC-closure value Σm_ν ≈ 0.0609 eV (from `scse_core.cc_neutrino_closure`
with log-log interpolation of manuscript anchors) lies INSIDE the
prediction range. -/

/-- Σm_ν from CC closure, computed numerically in
    `scse_core/cc_neutrino_closure.py`. -/
noncomputable def sigma_m_nu_CC_closure_eV : ℝ := 609 / 10000   -- 0.0609

/-- The CC-closure value falls inside the manuscript prediction range. -/
theorem CC_closure_in_prediction_range :
    sigma_m_nu_lower_eV < sigma_m_nu_CC_closure_eV ∧
    sigma_m_nu_CC_closure_eV < sigma_m_nu_upper_eV := by
  unfold sigma_m_nu_lower_eV sigma_m_nu_upper_eV sigma_m_nu_CC_closure_eV
  refine ⟨?_, ?_⟩ <;> norm_num

/-! ## Two-route self-consistency

The framework has TWO independent routes to the Σm_ν prediction:

* **Route 1** (Prop `thm:self-model-deficit`, −ζ'_vis(0) = 288):
  fixes the Yukawa product via the functional determinant constraint.

* **Route 2** (this file, CC closure via `Kappa2.lean`):
  fixes κ₂ via law-of-total-variance, ξ_R via see-saw cascade, M_R
  via Λ_c·exp(-ξ_R).

Both routes yield Σm_ν in the same narrow range [0.058, 0.063] eV,
which is the framework's **falsifiable prediction**. -/

theorem two_route_consistency :
    sigma_m_nu_lower_eV ≤ sigma_m_nu_CC_closure_eV ∧
    sigma_m_nu_CC_closure_eV ≤ sigma_m_nu_upper_eV := by
  rcases CC_closure_in_prediction_range with ⟨h1, h2⟩
  exact ⟨le_of_lt h1, le_of_lt h2⟩

end SpectralPhysics.Cosmology
