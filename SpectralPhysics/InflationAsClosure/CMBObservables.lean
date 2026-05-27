/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.InflationAsClosure.FrameworkPrimitives
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# CMB Observables — Framework Predictions vs Planck 2018

Formalizes the framework's predictions for the primordial scalar
power spectrum's shape parameters (n_s, r, α_s) and verifies the
match with Planck 2018 observations within 1σ.

## Pre-manuscript provenance

Manuscript v0.9.2 §`prop:two-phase` (line 8993): two-phase mode-
activation mechanism. CMB observables frozen at horizon exit
during inflation; manifest at recombination.

## Predictions at CMB pivot scale (k_pivot = 0.05 Mpc⁻¹)

At the framework's mode-activation index k=8 in Phase 1 (just before
Phase 2 transition):

| Observable | Framework | Planck 2018 (PR4) | σ deviation |
|------------|-----------|-------------------|-------------|
| n_s | 0.9665 (with κ_B correction) | 0.9649 ± 0.0042 | 0.39σ |
| r | 3.3×10⁻³ | <0.061 (95% CL) | consistent |
| α_s | -5.5×10⁻⁴ | -0.0045 ± 0.0067 | 0.59σ |
| A_s | 9.4×10⁻⁹ | 2.10×10⁻⁹ | factor 4.5 (closed via AsConventionChain) |

## What is proved

* `n_s_framework_within_1sigma`: framework's n_s prediction is within
  1σ of Planck 2018 central value.
* `r_framework_consistent_with_planck`: r is below the Planck 95% CL bound.
* `alpha_s_framework_within_1sigma`: framework's α_s is within 1σ.

## Tier

T1 for the inequalities (arithmetic verifiable). T2 for the
predictions themselves (depend on framework's mode-activation
mechanism + Hwang-Noh Jordan-frame derivation).
-/

namespace SpectralPhysics.InflationAsClosure.CMBObservables

open SpectralPhysics.InflationAsClosure

/-! ## Section 1: Framework predictions (numerical constants). -/

/-- Framework's n_s prediction at CMB pivot scale (k=8 in Phase 1
    + κ_B(k)=(36-k)/36 correction). -/
noncomputable def n_s_framework : ℝ := 0.9665

/-- Framework's r (tensor-to-scalar ratio) at N_e = 60. -/
noncomputable def r_framework : ℝ := 3.3e-3

/-- Framework's α_s (running) with κ_B correction at k=8. -/
noncomputable def alpha_s_framework : ℝ := -5.5e-4

/-! ## Section 2: Planck 2018 observational values. -/

/-- Planck 2018 (PR4) n_s central value. -/
noncomputable def n_s_planck_central : ℝ := 0.9649

/-- Planck 2018 n_s 1σ uncertainty. -/
noncomputable def n_s_planck_sigma : ℝ := 0.0042

/-- Planck 2018 r 95% CL upper bound. -/
noncomputable def r_planck_upper_95 : ℝ := 0.061

/-- Planck 2018 α_s central value. -/
noncomputable def alpha_s_planck_central : ℝ := -0.0045

/-- Planck 2018 α_s 1σ uncertainty. -/
noncomputable def alpha_s_planck_sigma : ℝ := 0.0067

/-! ## Section 3: Match theorems. -/

/-- **n_s match**: |n_s_framework - n_s_planck_central| ≤ n_s_planck_sigma
    (within 1σ).

    Numerically: |0.9665 - 0.9649| = 0.0016 ≤ 0.0042 ✓. -/
theorem n_s_framework_within_1sigma :
    |n_s_framework - n_s_planck_central| ≤ n_s_planck_sigma := by
  unfold n_s_framework n_s_planck_central n_s_planck_sigma
  rw [abs_le]
  constructor <;> norm_num

/-- **n_s match (refined)**: framework's n_s is within 0.39σ of central. -/
theorem n_s_framework_within_039_sigma :
    |n_s_framework - n_s_planck_central| ≤ 0.39 * n_s_planck_sigma := by
  unfold n_s_framework n_s_planck_central n_s_planck_sigma
  rw [abs_le]
  constructor <;> norm_num

/-- **r consistency**: framework's r is below Planck's 95% CL upper bound. -/
theorem r_framework_consistent_with_planck :
    r_framework < r_planck_upper_95 := by
  unfold r_framework r_planck_upper_95
  norm_num

/-- **α_s match**: framework's α_s is within 1σ of Planck central.

    Numerically: |-5.5e-4 - (-0.0045)| = |0.0040| = 0.004 ≤ 0.0067 ✓. -/
theorem alpha_s_framework_within_1sigma :
    |alpha_s_framework - alpha_s_planck_central| ≤ alpha_s_planck_sigma := by
  unfold alpha_s_framework alpha_s_planck_central alpha_s_planck_sigma
  rw [abs_le]
  constructor <;> norm_num

/-- **α_s match (refined)**: framework's α_s is within 0.59σ. -/
theorem alpha_s_framework_within_059_sigma :
    |alpha_s_framework - alpha_s_planck_central| ≤ 0.59 * alpha_s_planck_sigma := by
  unfold alpha_s_framework alpha_s_planck_central alpha_s_planck_sigma
  rw [abs_le]
  constructor <;> norm_num

/-! ## Section 4: Combined predictions match Planck. -/

/-- **Combined match theorem**: all three shape predictions (n_s, r, α_s)
    are simultaneously consistent with Planck 2018.

    This is the empirical anchor for the framework: NO free parameter
    is adjusted to match these; they're derived from the 5-sector +
    mode-activation structure. -/
theorem framework_cmb_match_planck :
    |n_s_framework - n_s_planck_central| ≤ n_s_planck_sigma ∧
    r_framework < r_planck_upper_95 ∧
    |alpha_s_framework - alpha_s_planck_central| ≤ alpha_s_planck_sigma := by
  refine ⟨n_s_framework_within_1sigma, r_framework_consistent_with_planck,
          alpha_s_framework_within_1sigma⟩

end SpectralPhysics.InflationAsClosure.CMBObservables
