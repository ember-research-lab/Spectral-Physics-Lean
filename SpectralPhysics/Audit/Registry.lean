/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Audit.Core
import SpectralPhysics.SelfModelDeficit.Kappa2
import SpectralPhysics.Predictions.ElectroweakRatio
import SpectralPhysics.InflationAsClosure.CombinedClosure
import SpectralPhysics.SelfModelDeficitRigorous.FaithfulnessSaturation
import SpectralPhysics.Cosmology.NeutrinoMassPrediction
import SpectralPhysics.Predictions.StrongCoupling

/-!
# Audit.Registry — the repository's real datum / prediction tags (2026-09-23)

Every tag cites the manuscript's OWN provenance statement. Source table:
`~/ember-tasks/physics-audit-provenance-2026-09-23/PROVENANCE.md` (tex line numbers below are
`spectral-physics.tex`, main, 2026-09-23). The detections are pinned as a **known-issues baseline**
(like `scripts/census/baseline.json`): fixing a circularity breaks its pin, and the pin is then
updated in the same change.
-/

namespace SpectralPhysics.Audit.Registry

open SpectralPhysics.SelfModelDeficit SpectralPhysics.InflationAsClosure
  SpectralPhysics.SelfModelDeficitRigorous.FaithfulnessSaturation SpectralPhysics.Cosmology

/-! ## Data: constants fixed by an observation (tex quote cited) -/

-- L17316-9 "Baker target derived from the observed cosmological constant"; L17573-5
audit_datum kappa2_hid "Lambda_obs"
-- L17745-7 "the located back-solve fixed by demanding … the observed cosmological constant"
audit_datum xi_R_CC "Lambda_obs"
-- L15664-6 "the boxed value is a back-solve"; L31290 "(Tier 3, back-solved; retagged 2026-09-06)"
audit_datum ewRatio "Tc/v"
-- L33383-5 "the Berry factor 500 was tuned against N_e = 60"
audit_datum delivered_enhancement "A_s"
-- CombinedClosure.lean:185-8 "A_s_predicted / A_s_observed … required ratio of about 510"
audit_datum required_enhancement "A_s"
-- L12528 "ε = √2 is a fit, not a derivation"; L13575 K = 1/3 + ε²/6
audit_datum leptonChannel "Koide"

/-! ## Declared inputs (hard-coded numbers with stated provenance; required by `#audit_literals`) -/

-- L4423 "[Tier 2: Framework theorem" (thm:two-constraints): the golden ratio
audit_input φ "DERIVED: golden ratio"
-- L15948 "The floor 0.058 eV is oscillation data."
audit_input sigma_m_nu_lower_eV "MEASURED: oscillation floor"
-- L15948 "CANNOT DERIVE as a framework prediction; survives as a conditional number on three posits."
audit_input sigma_m_nu_upper_eV "POSIT: upper anchor"
-- L17769-76 "every quantity feeding it traces back to the CC back-solve plus measured Δm²"
audit_datum sigma_m_nu_CC_closure_eV "Lambda_obs"

/-! ## Predictions (as presented in Lean) -/

audit_prediction kappa2_baker_target_match "Lambda_obs"
audit_prediction kappa2_centiunit_bracket "Lambda_obs"
audit_prediction ewRatio_agreement "Tc/v"
audit_prediction inflation_As_closure "A_s"
audit_prediction structural_residual_le_2_5_percent "A_s"
audit_prediction leptonChannel_koide "Koide"
audit_prediction faithfulness_saturation_koide "Koide"
-- negative control: fitting ξ_R to Λ_obs then predicting a DIFFERENT observable is legitimate
audit_prediction CC_closure_in_prediction_range "Sigma_mnu"
-- known blind spot: f₀ = τ (the α_s back-solve, L11368-72) is built into the formula; no constant to tag
audit_prediction strong_coupling_agreement "alpha_s"

/--
error: CIRCULAR: prediction SpectralPhysics.SelfModelDeficit.kappa2_baker_target_match ("Lambda_obs") depends on datum SpectralPhysics.SelfModelDeficit.kappa2_hid
CIRCULAR: prediction SpectralPhysics.SelfModelDeficit.kappa2_centiunit_bracket ("Lambda_obs") depends on datum SpectralPhysics.SelfModelDeficit.kappa2_hid
CIRCULAR: prediction ewRatio_agreement ("Tc/v") depends on datum ewRatio
CIRCULAR: prediction SpectralPhysics.InflationAsClosure.inflation_As_closure ("A_s") depends on datum SpectralPhysics.InflationAsClosure.delivered_enhancement
CIRCULAR: prediction SpectralPhysics.InflationAsClosure.inflation_As_closure ("A_s") depends on datum SpectralPhysics.InflationAsClosure.required_enhancement
CIRCULAR: prediction SpectralPhysics.InflationAsClosure.structural_residual_le_2_5_percent ("A_s") depends on datum SpectralPhysics.InflationAsClosure.delivered_enhancement
CIRCULAR: prediction SpectralPhysics.InflationAsClosure.structural_residual_le_2_5_percent ("A_s") depends on datum SpectralPhysics.InflationAsClosure.required_enhancement
CIRCULAR: prediction SpectralPhysics.SelfModelDeficitRigorous.FaithfulnessSaturation.leptonChannel_koide ("Koide") depends on datum SpectralPhysics.SelfModelDeficitRigorous.FaithfulnessSaturation.leptonChannel
-/
#guard_msgs in
#audit_circularity

/-! ## Literal laundering: a copied number carries no dependency edge -/

/-- info: audit_literals: every hard-coded number in the closure has declared provenance -/
#guard_msgs in
#audit_literals CC_closure_in_prediction_range strong_coupling_agreement ewRatio_agreement


end SpectralPhysics.Audit.Registry
