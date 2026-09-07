/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SelfModelDeficitRigorous.Theorem
import SpectralPhysics.SelfModelDeficitUnconditional.PredicateInventory
import SpectralPhysics.SelfModelDeficitUnconditional.PhysicalSpectrum
import SpectralPhysics.SelfModelDeficitUnconditional.CapacityBound
import SpectralPhysics.SelfModelDeficitUnconditional.NaturalityBound
import SpectralPhysics.SelfModelDeficitUnconditional.MellinFunctionalDet

/-!
# v0.9.2 Headline — Self-Model Deficit, *conditional* sandwich

The former `self_model_deficit_unconditional*` family took
`IsPhysicalSpectrum V` and concluded `negZetaPrimeAtZero V = 288`.
The only documented model of that predicate was
`informationContent V = 288`, so those theorems were
hypothesis=conclusion shells.

**2026-09-06.**  The opaque predicate and the two literature axioms
that it guarded are deleted.  The 288 result is the existing
sandwich from `SelfModelDeficitRigorous.Theorem` (lines 170–176 of
`Theorem.lean`), re-exported here under `_conditional` names:

    CompletenessAtLevel2 S (negZetaPrimeAtZero V) →
    SectorFaithfulNoDeadWeight S (negZetaPrimeAtZero V) →
    negZetaPrimeAtZero V = 288

The manuscript treats `−ζ̃′_vis(0) = 288` as H4, a Tier-3 posit
(`CapacityPosit288`) — not a derivation.  This module does not
discharge that posit.

## What is NOT claimed

* Not an unconditional proof.
* Not a Bekenstein / Mac Lane discharge of the two bounds.
* No theorem here has a hypothesis definitionally equal, or equal
  under a documented model of an opaque predicate, to its conclusion.
  The two sandwich hypotheses are genuine inequalities; their
  conjunction is equivalent to the conclusion only via `le_antisymm`
  plus combinatorial `dim H_hid = 288`.
-/

namespace SpectralPhysics.SelfModelDeficitUnconditional.UnconditionalGoal

open SpectralPhysics.SelfModelDeficitRigorous.SectorDecomposition
open SpectralPhysics.SelfModelDeficitRigorous.FaithfulState
open SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta
open SpectralPhysics.SelfModelDeficitRigorous.CompletenessBound
open SpectralPhysics.SelfModelDeficitRigorous.FaithfulnessBound
open SpectralPhysics.SelfModelDeficitRigorous.Theorem

/-- **Conditional headline — parameter form.**

For any sectored `*`-algebra `S` and any finite visible spectrum `V`,
if both named Level-2 bounds hold at `−ζ̃'_vis(0)`, then
`−ζ̃'_vis(0) = dim H_hid`.

This is `self_model_deficit_theorem` (the honest sandwich), renamed
from the retired `_unconditional_param`. -/
theorem self_model_deficit_conditional_param
    (S : SectoredStarAlgebra) (V : VisibleSpectrum)
    (h_completeness : CompletenessAtLevel2 S (negZetaPrimeAtZero V))
    (h_sector : SectorFaithfulNoDeadWeight S (negZetaPrimeAtZero V)) :
    negZetaPrimeAtZero V = (S.dimHid : ℝ) :=
  self_model_deficit_theorem S V h_completeness h_sector

/-- **Conditional headline — `informationContent` form of the
parameter equality.** -/
theorem self_model_deficit_conditional_explicit_param
    (S : SectoredStarAlgebra) (V : VisibleSpectrum)
    (h_completeness : CompletenessAtLevel2 S (negZetaPrimeAtZero V))
    (h_sector : SectorFaithfulNoDeadWeight S (negZetaPrimeAtZero V)) :
    informationContent V = (S.dimHid : ℝ) := by
  have h_eq := negZetaPrimeAtZero_eq V
  rw [← h_eq]
  exact self_model_deficit_conditional_param S V h_completeness h_sector

/-- **Conditional headline — specialised to the spectral-physics
decomposition.**

If both named Level-2 bounds hold at the canonical algebra
(`dim H_hid = 288` combinatorially), then `−ζ̃'_vis(0) = 288`.

This is `self_model_deficit_theorem_288`, renamed from the retired
`self_model_deficit_unconditional`.  It is **not** manuscript H4
discharged; H4 remains the Tier-3 posit `CapacityPosit288`. -/
theorem self_model_deficit_conditional
    (V : VisibleSpectrum)
    (h_completeness :
      CompletenessAtLevel2 spectralPhysicsSectoredAlgebra (negZetaPrimeAtZero V))
    (h_sector :
      SectorFaithfulNoDeadWeight spectralPhysicsSectoredAlgebra (negZetaPrimeAtZero V)) :
    negZetaPrimeAtZero V = (288 : ℝ) :=
  self_model_deficit_theorem_288 V h_completeness h_sector

/-- Variant in `informationContent` form. -/
theorem self_model_deficit_conditional_explicit
    (V : VisibleSpectrum)
    (h_completeness :
      CompletenessAtLevel2 spectralPhysicsSectoredAlgebra (negZetaPrimeAtZero V))
    (h_sector :
      SectorFaithfulNoDeadWeight spectralPhysicsSectoredAlgebra (negZetaPrimeAtZero V)) :
    informationContent V = (288 : ℝ) := by
  have h_eq := negZetaPrimeAtZero_eq V
  rw [← h_eq]
  exact self_model_deficit_conditional V h_completeness h_sector

end SpectralPhysics.SelfModelDeficitUnconditional.UnconditionalGoal
