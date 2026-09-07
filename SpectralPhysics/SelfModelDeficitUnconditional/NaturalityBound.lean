/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SelfModelDeficitRigorous.FaithfulnessBound
import SpectralPhysics.SelfModelDeficitUnconditional.PhysicalSpectrum

/-!
# Naturality (no-dead-weight) bound — Mac Lane axiom WITHDRAWN

This file previously declared `axiom NaturalityCoherence`, conditional
on the opaque predicate `IsPhysicalSpectrum`, and used it to discharge
`SectorFaithfulNoDeadWeight`.

That was unsound in three successive forms (paired with
`BekensteinInformationBound`):

1. Free `c : ℝ` (false at `c = dimHid−1`; `False` derivable).
2. Free `V : VisibleSpectrum` with computable `informationContent`
   (`NaturalityCoherence` alone derived `False` at single-mode `y = 1`).
3. Guarded only by `IsPhysicalSpectrum`, whose only documented model
   was `informationContent V = 288` — a hypothesis=conclusion shell.

**2026-09-06.**  The axiom is deleted.  No replacement axiom is
introduced.  The no-dead-weight bound remains the named hypothesis
`SectorFaithfulNoDeadWeight` at
`SelfModelDeficitRigorous.FaithfulState` / `FaithfulnessBound`,
consumed by `self_model_deficit_theorem_288`.

Mac Lane 1998 §VII is a literature citation for a *research-level*
category-theoretic translation that this repository does not claim.
-/

namespace SpectralPhysics.SelfModelDeficitUnconditional.NaturalityBound

/-! No declarations.  Callers use `SectorFaithfulNoDeadWeight` and
`sector_faithfulness_upper_bound` from the rigorous branch. -/

end SpectralPhysics.SelfModelDeficitUnconditional.NaturalityBound
