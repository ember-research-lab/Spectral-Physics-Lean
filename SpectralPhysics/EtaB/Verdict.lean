/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.EtaB.Comparison

/-!
# The framework's standing prediction for `η_B`: the verdict

Two considerations bear on the disambiguation between Formula A
(`λ^14`, v0.9 prop:eta) and Formula B (`J²/2`, sandbox
`sr-resonance-yukawa.tex` line 248):

1. **Numerical match to observation.**  The Lean comparison in
   `Comparison.lean` proves
     `|η_B^B − η_B^obs| < |η_B^A − η_B^obs|`
   (Tier 1, no axioms beyond `etaB_observed_value` and
   `Jarlskog_value`).  Specifically:
     `|dev_B| = 1.6 × 10⁻¹⁰` (exact)
     `|dev_A| ∈ (1.8 × 10⁻¹⁰, 2.0 × 10⁻¹⁰)`
   so Formula B wins by `~2-4 × 10⁻¹¹`.

2. **Documentation precedence.**  The sandbox
   `yukawa/sr-resonance-yukawa.tex` (line 248) explicitly states
   that Formula B is "a clean derivation replacing the heuristic
   `λ^14`" — i.e. the manuscript itself deprecates Formula A in
   favour of Formula B.  v0.9 has not yet been updated to reflect
   this, so v0.9's `prop:eta` is the *standing inconsistency*,
   not a competing claim.

Both criteria point in the same direction.  The framework's
endorsed prediction for the cosmic baryon-to-photon ratio is
**Formula B**: `η_B = J²/2`.

> ⚠️  **Honest caveat.**  The numerical superiority of Formula B
>     established here was *not* the original disambiguation
>     hypothesis: the task spec quoted Formula A as giving
>     `≈ 4.4 × 10⁻¹⁰`, which would have placed it on the *same*
>     side of the observed value as Formula B and made the choice
>     turn on a small `0.1 × 10⁻¹⁰` gap.  Once Lean enforced an
>     actual `λ_C^14` evaluation, the value came out at
>     `8.02 × 10⁻¹⁰` — Formula A *overshoots* the observed value.
>     Formula B *undershoots*.  This makes the disambiguation
>     clean rather than tied.

## References

* v0.9 manuscript, Prop. `prop:eta` (line ~14594):  Formula A.
* Sandbox `yukawa/sr-resonance-yukawa.tex` line 248:  Formula B
  deprecates Formula A.
* PDG 2024 CKM review:  `J ≈ 3.0 × 10⁻⁵`.
* Planck 2018, A&A 641 A6:  `η_B^obs ≈ 6.10 × 10⁻¹⁰`.
-/

namespace SpectralPhysics.EtaB

noncomputable section

open Real

/-! ## The framework's standing prediction -/

/-- **Definition (framework verdict).**

    The cosmic baryon-to-photon ratio predicted by the spectral-physics
    framework, as endorsed by:

    * Numerical match (Lean-checked: Formula B is closer to Planck 2018).
    * Documentation precedence (sandbox `sr-resonance-yukawa.tex`
      line 248 deprecates Formula A in favour of Formula B).

    Quantitative content: `framework_endorsed_etaB = 4.5 × 10⁻¹⁰`,
    derived from the PDG Jarlskog invariant `J ≈ 3.00 × 10⁻⁵` via
    `η_B = J²/2`. -/
def framework_endorsed_etaB : ℝ := etaB_FormulaB

/-- The framework verdict reduces to Formula B by definition. -/
theorem framework_endorsed_eq_FormulaB :
    framework_endorsed_etaB = etaB_FormulaB := rfl

/-- The framework verdict's exact numerical value, given the PDG
    `Jarlskog_value` axiom: `4.5 × 10⁻¹⁰`. -/
theorem framework_endorsed_value : framework_endorsed_etaB = 4.5e-10 := by
  rw [framework_endorsed_eq_FormulaB]
  exact etaB_FormulaB_exact

/-- The framework verdict is strictly closer to the observed value
    than the deprecated Formula A. -/
theorem framework_endorsed_beats_FormulaA :
    |framework_endorsed_etaB - etaB_observed| <
    |etaB_FormulaA - etaB_observed| := by
  rw [framework_endorsed_eq_FormulaB]
  exact abs_deviation_compare

/-- The framework verdict is strictly positive. -/
theorem framework_endorsed_pos : 0 < framework_endorsed_etaB := by
  rw [framework_endorsed_eq_FormulaB]
  exact etaB_FormulaB_pos

/-- The framework verdict undershoots the observed value
    (by `1.6 × 10⁻¹⁰`).  Restated for callers. -/
theorem framework_endorsed_lt_observed :
    framework_endorsed_etaB < etaB_observed := by
  rw [framework_endorsed_eq_FormulaB]
  exact etaB_FormulaB_lt_observed

end

end SpectralPhysics.EtaB
