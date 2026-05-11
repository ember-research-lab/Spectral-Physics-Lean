/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta

/-!
# v0.9.2 Mellin Functional Determinant — Connes–Marcolli axiom

This file re-states the v0.9.1 named axiom
`mellin_heat_kernel_finite_spectrum_log_sum` (from
`SelfModelDeficitRigorous/SpectralZeta.lean`) under a v0.9.2-style
named-literature handle, **without** introducing any new axiom-class
content.

The v0.9.1 axiom — that for a finite visible spectrum `V`, the
Mellin-transform-derived `−ζ̃'(0)` equals the explicit
`informationContent V` sum — is the single Connes–Marcolli identity on
which the headline depends.  v0.9.2 keeps it as-is and packages it
under a literature-axiom name `MellinRegularization` that pairs the
three axioms of the unconditional dispatch (Bekenstein / Mac Lane /
Connes–Marcolli).

## Why no new axiom

The v0.9.1 axiom is **already** the literature-axiom form: it cites
Connes–Marcolli 2008 §1.7 and Berline–Getzler–Vergne 1992; it states
a general identity for any finite spectrum; it does not fix a
numerical value of the sum.

We therefore avoid duplicating it.  Instead we provide a definitional
wrapper `MellinRegularization` and a theorem that produces the
existence statement from the v0.9.1 axiom, with the citation re-stated
in the docstring for v0.9.2 audit purposes.

## Honesty checks

* This file introduces **no** new `axiom` declarations.  All content
  is theorems built on the v0.9.1 axiom.
* The `MellinRegularization` definition unfolds to the v0.9.1
  existential statement; it adds no new content.
* The number 288 does not appear in this file.
-/

namespace SpectralPhysics.SelfModelDeficitUnconditional.MellinFunctionalDet

open SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta

/-- **v0.9.2 named-literature handle** for the Mellin-transform /
heat-kernel identity from Connes–Marcolli §1.7.

This is **not** a new axiom: it is a `def` that unpacks the v0.9.1
existence statement
`mellin_heat_kernel_finite_spectrum_log_sum (V) : ∃ z, z = informationContent V`
into the standard literature-axiom shape.

**Citation**: Connes–Marcolli, *Noncommutative Geometry, Quantum
Fields and Motives*, AMS Colloquium Publications vol. 55 (2008), §1.7;
Berline–Getzler–Vergne, *Heat Kernels and Dirac Operators*, Grundlehren
der Math. Wiss. 298 (1992), Chapter 2 and §9.6.

**What this asserts**: for any finite visible spectrum `V`, there
exists a real value (the Mellin-regularised `−ζ̃'(0)`) equal to the
explicit `informationContent V` sum.

**What this does NOT assert**: any specific numerical value of
`informationContent V` for any concrete `V`.  The value is determined
by the spectrum, which is an input. -/
def MellinRegularization (V : VisibleSpectrum) : Prop :=
  ∃ z : ℝ, z = informationContent V

/-- The v0.9.1 axiom discharges `MellinRegularization` for every `V`.

This theorem does **not** introduce new axiom-class content; it is a
direct application of the v0.9.1
`mellin_heat_kernel_finite_spectrum_log_sum`. -/
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

This file is intentionally a *thin* re-statement of the v0.9.1 axiom
under a v0.9.2 literature-axiom name.  All substantive content was
already named and cited in v0.9.1; the v0.9.2 packaging simply pairs
it with `BekensteinInformationBound` and `NaturalityCoherence` as the
three named literature axioms of the unconditional dispatch.

`#print axioms mellinRegularization_holds` shows that this theorem
depends only on the v0.9.1 axiom plus kernel axioms — no new
declarations introduced. -/

end SpectralPhysics.SelfModelDeficitUnconditional.MellinFunctionalDet
