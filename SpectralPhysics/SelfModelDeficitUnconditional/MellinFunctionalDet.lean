/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta

/-!
# v0.9.2 Mellin Functional Determinant — alias, not an axiom

`mellin_heat_kernel_finite_spectrum_log_sum` in
`SelfModelDeficitRigorous/SpectralZeta.lean` is a **theorem**
(`⟨informationContent V, rfl⟩`), a reification of the audit-caught
vacuous-marker axiom named after Connes–Marcolli §1.7.  This file
packages that theorem under the handle `MellinRegularization`.

It does **not** pair with Bekenstein / Mac Lane axioms: those are
deleted (2026-09-06).  It does not fix `informationContent` to 288.

## Honesty checks

* This file introduces **no** `axiom` declarations.
* The `MellinRegularization` definition unfolds to `∃ z, z = informationContent V`.
* The number 288 does not appear in this file.
-/

namespace SpectralPhysics.SelfModelDeficitUnconditional.MellinFunctionalDet

open SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta

/-- Handle for the Mellin alias.

This is **not** a new axiom: it unpacks
`mellin_heat_kernel_finite_spectrum_log_sum (V) : ∃ z, z = informationContent V`
(a theorem, `⟨informationContent V, rfl⟩`).

It does not assert any specific numerical value of
`informationContent V`. -/
def MellinRegularization (V : VisibleSpectrum) : Prop :=
  ∃ z : ℝ, z = informationContent V

/-- The SpectralZeta theorem discharges `MellinRegularization` for every `V`. -/
theorem mellinRegularization_holds (V : VisibleSpectrum) :
    MellinRegularization V :=
  mellin_heat_kernel_finite_spectrum_log_sum V

/-- The `negZetaPrimeAtZero` value of v0.9.1 is the witness of
`MellinRegularization`. -/
theorem negZetaPrimeAtZero_witnesses_mellinRegularization
    (V : VisibleSpectrum) :
    negZetaPrimeAtZero V = informationContent V :=
  negZetaPrimeAtZero_eq V

/-! ### Audit note

Thin alias of the SpectralZeta theorem.  No axiom is introduced.
The Connes–Marcolli identity itself is not formalized; the Lean
content is `∃ z, z = informationContent V`. -/

end SpectralPhysics.SelfModelDeficitUnconditional.MellinFunctionalDet
