/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SelfModelDeficitRigorous.SectorDecomposition
import SpectralPhysics.SelfModelDeficitRigorous.FaithfulState
import SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta
import SpectralPhysics.SelfModelDeficitRigorous.CompletenessBound
import SpectralPhysics.SelfModelDeficitRigorous.FaithfulnessBound
import SpectralPhysics.SelfModelDeficitRigorous.Theorem

/-!
# v0.9.1 → v0.9.2 Predicate Inventory

This file formally enumerates the predicate hypotheses that the v0.9.1
branch `compute/self-model-deficit-rigorous` left open, classifies each
by closure status, and locates the named literature axioms used by the
v0.9.2 sharpening.

## Honest accounting

The v0.9.1 `STATUS.md` left the v0.9 Proposition 23.10 result
conditional on **two** Prop-valued predicates supplied as hypotheses:

* `CompletenessAtLevel2 S infContent` — the Level-2 information-capacity
  bound stating `infContent ≤ (dim H_hid : ℝ)`.
* `SectorFaithfulNoDeadWeight S infContent` — the no-dead-weight
  partial-trace bound `(dim H_hid : ℝ) ≤ infContent`.

It also depended on one named axiom:

* `mellin_heat_kernel_finite_spectrum_log_sum` — the
  Mellin–heat-kernel identity (Connes–Marcolli §1.7).

The combinatorial backbone (`HiddenSectorDim = 288` from
`384 − 96 = 288`) was unconditional.

## v0.9.2 closure status

For each v0.9.1 predicate we classify:

* **Closable in Lean now** — provable from Mathlib + existing modules.
* **Closable from named literature axiom** — discharged by a *single*
  cited theorem, leaving exactly one axiom per predicate.
* **Genuinely open** — remains as predicate-hypothesis with no closing
  axiom yet, deferred to v1.0+.

For the self-model deficit content, the v0.9.2 verdict (see
`Verdict.lean`) is:

| v0.9.1 predicate | v0.9.2 closure | Named axiom |
|---|---|---|
| `CompletenessAtLevel2` | **closable from literature axiom** | `BekensteinInformationBound` (`CapacityBound.lean`) |
| `SectorFaithfulNoDeadWeight` | **closable from literature axiom** | `NaturalityCoherence` (`NaturalityBound.lean`) |
| `mellin_heat_kernel_finite_spectrum_log_sum` | named axiom (unchanged from v0.9.1) | `MellinRegularization` (`MellinFunctionalDet.lean`) |

Net: the v0.9.1 "two open predicates with no closing axiom" become
**three named literature axioms**.  That reduction — open content to
explicit, cited, *general* literature theorems — is the v0.9.2 progress
the deferred-list category C.1 asks for.

The verdict is **PARTIAL**.  We do not claim to close the result; we
claim to have reduced its open content to three named literature axioms
whose closure is a research-level operator-algebra question (the same
6–12 month estimate the v0.9.2 deferred list gives for C.1).
-/

namespace SpectralPhysics.SelfModelDeficitUnconditional.PredicateInventory

open SpectralPhysics.SelfModelDeficitRigorous.SectorDecomposition
open SpectralPhysics.SelfModelDeficitRigorous.FaithfulState
open SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta

/-! ### Inventory of v0.9.1 predicates (as defs, for `#check`) -/

/-- v0.9.1 predicate (i): the Level-2 capacity (completeness) bound.

This is **identical** to `CompletenessAtLevel2` from
`SelfModelDeficitRigorous.FaithfulState`; we re-name it here in the
inventory namespace to flag that the v0.9.2 closure attempt provides
a literature axiom (`BekensteinInformationBound`) that discharges it. -/
def Predicate_CompletenessAtLevel2 (S : SectoredStarAlgebra)
    (infContent : ℝ) : Prop :=
  CompletenessAtLevel2 S infContent

/-- v0.9.1 predicate (ii): the no-dead-weight (sector-faithfulness)
bound.

Same relationship to v0.9.1: this is `SectorFaithfulNoDeadWeight`,
re-named in the inventory namespace.  The v0.9.2 closure provides
`NaturalityCoherence` from monoidal-category coherence
(Mac Lane §VII). -/
def Predicate_SectorFaithfulNoDeadWeight (S : SectoredStarAlgebra)
    (infContent : ℝ) : Prop :=
  SectorFaithfulNoDeadWeight S infContent

/-- The v0.9.1 conjunction `Axiom3Level2`. -/
def Predicate_Axiom3Level2 (S : SectoredStarAlgebra) (infContent : ℝ) :
    Prop :=
  Axiom3Level2 S infContent

/-- The combinatorial 288 (unconditional Tier-1 Lean result).

This is *not* one of the open predicates; we list it here as a
sanity-check that the inventory unfolds correctly. -/
theorem hidden_sector_unconditional :
    spectralPhysicsDecomposition.hidden = 288 := by decide

/-- The conjunction predicate unfolds to its v0.9.1 form. -/
theorem axiom3_level2_unfold (S : SectoredStarAlgebra) (c : ℝ) :
    Predicate_Axiom3Level2 S c ↔
      Predicate_CompletenessAtLevel2 S c ∧
      Predicate_SectorFaithfulNoDeadWeight S c := by
  rfl

/-! ### What v0.9.2 changes

`CapacityBound.lean` introduces `BekensteinInformationBound` as a named
literature axiom (citing Bekenstein 1981) and derives
`Predicate_CompletenessAtLevel2` from it for any
`(S, V)` whose visible-sector entropy is bounded by `dim H_hid` (the
"capacity ≥ information" direction of the Bekenstein universal bound).

`NaturalityBound.lean` introduces `NaturalityCoherence` (citing
Mac Lane *Categories for the Working Mathematician* §VII) and derives
`Predicate_SectorFaithfulNoDeadWeight` from it.

`MellinFunctionalDet.lean` re-states the v0.9.1
`mellin_heat_kernel_finite_spectrum_log_sum` as `MellinRegularization`
with the same citation (Connes–Marcolli §1.7).

The three named axioms are the **only** new axiom-class dependencies of
the v0.9.2 headline theorem.  This is verified by `#print axioms` in
`UnconditionalGoal.lean`.
-/

/-! ### `#check` audit (compile-time inventory) -/

example (S : SectoredStarAlgebra) (c : ℝ) :
    Predicate_CompletenessAtLevel2 S c = (c ≤ (S.dimHid : ℝ)) :=
  rfl

example (S : SectoredStarAlgebra) (c : ℝ) :
    Predicate_SectorFaithfulNoDeadWeight S c = ((S.dimHid : ℝ) ≤ c) :=
  rfl

end SpectralPhysics.SelfModelDeficitUnconditional.PredicateInventory
