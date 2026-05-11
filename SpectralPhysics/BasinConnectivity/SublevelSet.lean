/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.KSRCompactness.Verdict
import Mathlib.Topology.Connected.PathConnected

/-!
# Sublevel sets of a functional `F : 𝒦_SR → ℝ`

This file defines the sublevel set machinery used by v0.9.2 deferred
item **G.3** (v0.9 line 16763): the v0.9 "basin is everything" claim
states that for the SAGF functional `F : 𝒦_SR → ℝ`, the sublevel sets

  `{ T ∈ 𝒦_SR : F(T) ≤ c }`

are connected (in the trace-norm topology on `𝒦_SR`).  Baker isolation
gives discreteness of critical points; it does **not** give
connectedness of the basins between them.

This module carries only the **structural** content:

* `sublevel F c` — the sublevel set as a `Set KSR`.
* `SAGFfunctional` — abstract carrier; the *real* `F` is the v0.9 §47
  spectral action.  We do NOT axiomatise its analytic structure here;
  open content is carried in `ConnectednessPredicate.lean`.

The topology on `KSR` is the one inherited from
`SpectralPhysics.KSRCompactness.RellichKondrachov` (the placeholder
discrete topology pending Mathlib's Schatten-1 ideal infrastructure).
**This is a documented limitation**, recorded in `STATUS.md`: the
genuine `IsPathConnected` content of the v0.9 claim refers to the
trace-norm topology; the discrete-topology shadow gives a strictly
*stronger* statement (since fewer sets are path-connected under the
discrete topology than under the trace-norm one), so a closure here
under discrete topology would not imply the v0.9 framework claim
without the topological refinement.  Accordingly we keep the
sublevel-set machinery topology-agnostic and state the framework's
claim and obstructions in `ConnectednessPredicate.lean` /
`MorseObstruction.lean` as **predicate-carried** open content.

## References

* v0.9 line 16763 — the basin-connectivity claim and its admission as
  a self-objection.
* `pre_geometric/v091_v092_split_audit/v092_deferred.md` §G.3.
* Bredon, G.E. (1993), *Topology and Geometry*, GTM 139, Springer,
  §III.4 (path-connectedness; sublevel sets of continuous functions).
* Morse, M. (1934), *The Calculus of Variations in the Large*,
  AMS Colloquium Publications 18, Ch. VI (critical-point theory and
  sublevel-set topology).
-/

noncomputable section

open Set

namespace SpectralPhysics.BasinConnectivity

open SpectralPhysics.KSRCompactness

/-! ## The SAGF functional carrier

Per v0.9 §47, the SAGF functional `F : 𝒦_SR → ℝ` is the
algebra-to-geometry transition spectral action.  Its concrete
analytic form (heat-kernel expansion, Seeley–DeWitt tower) is
**not** what this module needs: it needs only that `F` is a
real-valued functional on `𝒦_SR`.

We therefore carry `F` as an abstract `KSR → ℝ` and predicate-state
its required properties downstream (coercivity, Palais–Smale,
unique-minimum). -/

/-- Abstract SAGF functional `F : 𝒦_SR → ℝ`.

The *concrete* identity of `SAGFfunctional` (the v0.9 spectral
action) is open content per the v0.9.2 deferred §G.3 brief; we
carry it as a noncomputable opaque function and let downstream
predicates do the work.  This is the same "function as data, not
definition" pattern used in `OP3/SCSEClosureSystem.lean` for the
SCSE root finder. -/
noncomputable opaque SAGFfunctional : KSR → ℝ

/-! ## Sublevel sets

`sublevel F c := { T : KSR | F T ≤ c }`. -/

/-- The **sublevel set** `{ T : 𝒦_SR : F T ≤ c }`. -/
def sublevel (F : KSR → ℝ) (c : ℝ) : Set KSR := { T | F T ≤ c }

/-- Monotonicity of sublevel sets in the threshold `c`: larger `c`
gives a larger sublevel set. -/
theorem sublevel_subset_of_le {F : KSR → ℝ} {c c' : ℝ} (h : c ≤ c') :
    sublevel F c ⊆ sublevel F c' := by
  intro T hT
  exact le_trans hT h

/-- Membership characterisation. -/
theorem mem_sublevel {F : KSR → ℝ} {c : ℝ} {T : KSR} :
    T ∈ sublevel F c ↔ F T ≤ c := Iff.rfl

/-- The zero kernel lies in `sublevel SAGFfunctional c` iff
`SAGFfunctional KSR.zero ≤ c`.  This is a *signpost* — the
concrete value of `SAGFfunctional KSR.zero` is open content and
NOT discharged. -/
theorem zero_mem_sublevel_iff {c : ℝ} :
    KSR.zero ∈ sublevel SAGFfunctional c ↔ SAGFfunctional KSR.zero ≤ c :=
  Iff.rfl

/-! ## Empty / universal sublevel set conditions

If `c < F T` for all `T`, the sublevel set is empty.  If `c` is
above `sup F`, it is everything.  These are *vacuous* edge cases —
mentioned here so the reader can see we are NOT relying on them. -/

/-- Below the infimum of `F` the sublevel set is empty. -/
theorem sublevel_empty_of_lt {F : KSR → ℝ} {c : ℝ}
    (h : ∀ T : KSR, c < F T) :
    sublevel F c = ∅ := by
  ext T
  simp only [sublevel, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
  exact h T

end SpectralPhysics.BasinConnectivity

end
