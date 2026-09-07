/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SelfModelDeficitRigorous.CompletenessBound
import SpectralPhysics.SelfModelDeficitUnconditional.PhysicalSpectrum

/-!
# Capacity bound — Bekenstein literature axiom WITHDRAWN

This file previously declared `axiom BekensteinInformationBound`,
conditional on the opaque predicate `IsPhysicalSpectrum`, and used it
to discharge `CompletenessAtLevel2`.

That was unsound in three successive forms:

1. Free `c : ℝ` (false at `c = dimHid+1`; `False` derivable).
2. Free `V : VisibleSpectrum` with computable `informationContent`
   (false at the single-mode `y = 1` spectrum).
3. Guarded only by `IsPhysicalSpectrum`, whose only documented model
   was `informationContent V = 288` — a hypothesis=conclusion shell.

**2026-09-06.**  The axiom is deleted.  No replacement axiom is
introduced.  The Level-2 completeness bound remains the named
hypothesis `CompletenessAtLevel2` at
`SelfModelDeficitRigorous.FaithfulState` / `CompletenessBound`,
consumed by `self_model_deficit_theorem_288`.

Bekenstein 1981 is a literature citation for a *research-level*
operator-algebra translation that this repository does not claim.
The manuscript H4 identification `−ζ̃′_vis(0) = 288` is the named
posit `CapacityPosit288` (Tier 3, not derived).
-/

namespace SpectralPhysics.SelfModelDeficitUnconditional.CapacityBound

/-! No declarations.  Callers use `CompletenessAtLevel2` and
`completeness_lower_bound` from the rigorous branch. -/

end SpectralPhysics.SelfModelDeficitUnconditional.CapacityBound
