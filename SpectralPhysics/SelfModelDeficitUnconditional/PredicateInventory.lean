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
# v0.9.1 Predicate Inventory (2026-09-06 honesty pass)

The v0.9.1 `STATUS.md` left v0.9 Proposition 23.10 conditional on
**two** Prop-valued predicates:

* `CompletenessAtLevel2 S infContent` — `infContent ≤ (dim H_hid : ℝ)`
* `SectorFaithfulNoDeadWeight S infContent` — `(dim H_hid : ℝ) ≤ infContent`

v0.9.2 claimed to discharge both from named literature axioms
(`BekensteinInformationBound`, `NaturalityCoherence`) plus an opaque
physicality predicate `IsPhysicalSpectrum`.  Those three axioms are
**deleted** (2026-09-06): they were unsound, then shells under the
only documented model `IsPhysicalSpectrum V := (informationContent V = 288)`.

**Current status of the inventory:**

| v0.9.1 predicate | status | closer |
|---|---|---|
| `CompletenessAtLevel2` | **open named hypothesis** | none (Bekenstein axiom withdrawn) |
| `SectorFaithfulNoDeadWeight` | **open named hypothesis** | none (Mac Lane axiom withdrawn) |
| Mellin alias `negZetaPrimeAtZero` | theorem (`⟨informationContent V, rfl⟩`) | not a literature axiom |

The combinatorial backbone (`HiddenSectorDim = 288` from
`384 − 96 = 288`) is unconditional.

The 288 *spectral* identification is manuscript H4, a Tier-3 posit
(`CapacityPosit288`) — not derived.  The Lean theorem is the
sandwich `self_model_deficit_theorem_288`.
-/

namespace SpectralPhysics.SelfModelDeficitUnconditional.PredicateInventory

open SpectralPhysics.SelfModelDeficitRigorous.SectorDecomposition
open SpectralPhysics.SelfModelDeficitRigorous.FaithfulState
open SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta

/-! ### Inventory of v0.9.1 predicates (as defs, for `#check`) -/

/-- v0.9.1 predicate (i): the Level-2 capacity (completeness) bound.

Identical to `CompletenessAtLevel2`.  Remains an open named
hypothesis; the Bekenstein literature axiom that claimed to
discharge it is withdrawn. -/
def Predicate_CompletenessAtLevel2 (S : SectoredStarAlgebra)
    (infContent : ℝ) : Prop :=
  CompletenessAtLevel2 S infContent

/-- v0.9.1 predicate (ii): the no-dead-weight (sector-faithfulness)
bound.

Identical to `SectorFaithfulNoDeadWeight`.  Remains an open named
hypothesis; the Mac Lane literature axiom that claimed to discharge
it is withdrawn. -/
def Predicate_SectorFaithfulNoDeadWeight (S : SectoredStarAlgebra)
    (infContent : ℝ) : Prop :=
  SectorFaithfulNoDeadWeight S infContent

/-- The v0.9.1 conjunction `Axiom3Level2`. -/
def Predicate_Axiom3Level2 (S : SectoredStarAlgebra) (infContent : ℝ) :
    Prop :=
  Axiom3Level2 S infContent

/-- The combinatorial 288 (unconditional Tier-1 Lean result). -/
theorem hidden_sector_unconditional :
    spectralPhysicsDecomposition.hidden = 288 := by decide

/-- The conjunction predicate unfolds to its v0.9.1 form. -/
theorem axiom3_level2_unfold (S : SectoredStarAlgebra) (c : ℝ) :
    Predicate_Axiom3Level2 S c ↔
      Predicate_CompletenessAtLevel2 S c ∧
      Predicate_SectorFaithfulNoDeadWeight S c := by
  rfl

/-! ### `#check` audit (compile-time inventory) -/

example (S : SectoredStarAlgebra) (c : ℝ) :
    Predicate_CompletenessAtLevel2 S c = (c ≤ (S.dimHid : ℝ)) :=
  rfl

example (S : SectoredStarAlgebra) (c : ℝ) :
    Predicate_SectorFaithfulNoDeadWeight S c = ((S.dimHid : ℝ) ≤ c) :=
  rfl

end SpectralPhysics.SelfModelDeficitUnconditional.PredicateInventory
