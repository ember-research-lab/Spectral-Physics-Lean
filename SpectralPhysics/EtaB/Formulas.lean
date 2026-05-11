/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Predictions.CabibboAngle

/-!
# Two competing formulas for the baryon-asymmetry parameter `η_B`

The spectral-physics framework has two distinct closed-form predictions
for the cosmic baryon-to-photon ratio `η_B`:

* **Formula A** — `η_B = λ^14`  (v0.9 manuscript, Prop. `prop:eta`,
  approximate line 14594).  Here `λ` is the Cabibbo parameter, which
  the framework derives in v0.9 Theorem 40.2 (`thm:cabibbo`) as
  `(150 − 23·√5)/440 ≈ 0.224024`.

* **Formula B** — `η_B = J² / 2`  (sandbox `sr-resonance-yukawa.tex`
  line 248, which explicitly *deprecates* Formula A).  Here `J` is the
  Jarlskog CP-violation invariant of the CKM matrix, taken from the
  observed value `J ≈ 3.0 × 10⁻⁵` (PDG / Particle Data Group review
  of CP violation).

Numerically the two predictions are close (`λ^14 ≈ 4.4 × 10⁻¹⁰`,
`J²/2 ≈ 4.5 × 10⁻¹⁰`), and the observed value (Planck 2018 CMB) is
`η_B ≈ 6.1 × 10⁻¹⁰`.  This file states both formulas as named Lean
definitions; the comparison and the framework verdict live in
`Comparison.lean` and `Verdict.lean` respectively.

## References

* Ben-Shalom, *Spectral Physics* v0.9, Prop. `prop:eta`     (Formula A)
* `yukawa/sr-resonance-yukawa.tex` lines 235, 248, 261-263  (Formula B)
* PDG 2024 CKM review                                       (J value)
* Planck 2018, Aghanim et al., A&A 641 A6 (2020)            (η_B obs)
-/

namespace SpectralPhysics.EtaB

noncomputable section

open Real

/-! ## Formula A — `η_B = λ^14` -/

/-- The Cabibbo parameter `λ_C`, re-exported from
    `SpectralPhysics.Predictions.CabibboAngle` for use in this section.
    Closed form: `λ_C = (150 − 23√5)/440`. -/
noncomputable def lambdaC : ℝ := cabibboParam

/-- Closed form of `λ_C`, inherited from `CabibboAngle`. -/
theorem lambdaC_closed_form :
    lambdaC = (150 - 23 * Real.sqrt 5) / 440 :=
  cabibbo_closed_form

/-- **Formula A:** the v0.9 prediction `η_B = λ_C^14`.

    This is the baryon-asymmetry expression that appears in
    Prop. `prop:eta` of the v0.9 manuscript.  The sandbox
    `sr-resonance-yukawa.tex` (line 248) labels this formula
    as a *heuristic* that is *replaced* by Formula B, but it
    remains the standing formula in v0.9 until the manuscript
    is updated. -/
def etaB_FormulaA : ℝ := lambdaC ^ 14

/-! ## Formula B — `η_B = J²/2`

    The Jarlskog invariant `J` is an *observational* CP-violation
    parameter, not derived from the framework axioms (the framework
    fixes the CKM *phase* `δ_CKM = π/φ²`, but the magnitude of `J`
    requires the absolute Cabibbo angle plus the other two CKM
    angles which the framework does not currently predict to PDG
    precision).  Therefore `Jarlskog` is introduced as a named
    axiom citing the PDG 2024 value. -/

/-- **Named axiom (observational input).**

    The Jarlskog CP-violation invariant of the CKM matrix.

    Numerical value `J = 3.00 × 10⁻⁵` from PDG 2024 CKM review
    (central best-fit value `J = 3.00^{+0.15}_{−0.09} × 10⁻⁵`).

    This is *not* a framework-derived quantity; it is an
    observational input to Formula B.  We axiomatize the value
    rather than smuggle a numerical literal: the named axiom
    makes the dependence on PDG explicit and reviewable. -/
axiom Jarlskog : ℝ

/-- The Jarlskog invariant is positive (PDG central value is positive). -/
axiom Jarlskog_pos : 0 < Jarlskog

/-- The PDG central value: `J = 3.00 × 10⁻⁵`. -/
axiom Jarlskog_value : Jarlskog = 3.00e-5

/-- **Formula B:** the sandbox prediction `η_B = J² / 2`.

    Derivation outline (per `sr-resonance-yukawa.tex` lines 261–263):
    the determinant of the CKM commutator `[H_u, H_d]` is the
    "tuning-fork" structure whose magnitude is `J`, and the
    asymmetric leptogenesis-like channel gives a factor of `1/2`.
    Formula B "should hold regardless of the rank question — it
    depends only on the CKM phase (which is fixed from the
    framework) and the Jarlskog invariant structure." -/
def etaB_FormulaB : ℝ := Jarlskog ^ 2 / 2

/-! ## Sanity-level relations (Tier 1, machine-checked) -/

/-- `λ_C` is strictly positive. -/
theorem lambdaC_pos : 0 < lambdaC := by
  unfold lambdaC cabibboParam
  have hτ : 0 < τ := by simp only [τ]; unfold φ; positivity
  positivity

/-- Formula A is strictly positive (since `λ_C > 0`). -/
theorem etaB_FormulaA_pos : 0 < etaB_FormulaA := by
  unfold etaB_FormulaA
  exact pow_pos lambdaC_pos 14

/-- Formula A is non-negative. -/
theorem etaB_FormulaA_nonneg : 0 ≤ etaB_FormulaA :=
  le_of_lt etaB_FormulaA_pos

/-- Formula B is strictly positive. -/
theorem etaB_FormulaB_pos : 0 < etaB_FormulaB := by
  unfold etaB_FormulaB
  have hJ := Jarlskog_pos
  positivity

end

end SpectralPhysics.EtaB
