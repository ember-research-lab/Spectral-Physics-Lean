/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.BasinConnectivity.SublevelSet

/-!
# The basin-connectivity predicate (v0.9 line 16763)

This file states v0.9's "basin is everything" claim as a `Prop`
predicate over functionals `F : 𝒦_SR → ℝ`:

  `BasinConnectivity F := ∀ c, IsPathConnected (sublevel F c)`.

The framework claim under audit is
`BasinConnectivity SAGFfunctional` — that every sublevel set of the
SAGF functional is path-connected in the trace-norm topology on
`𝒦_SR`.

**This Prop is NOT discharged here.**  It is the *open content* of
v0.9.2 deferred item G.3.  Downstream files (`PalaisSmaleApproach`,
`MorseObstruction`, `Verdict`) state the conditional theorems and
the structural obstruction that together justify the
**CONDITIONAL** verdict.

## Why not just axiomatise `BasinConnectivity SAGFfunctional`?

That would be the **conclusion-as-axiom** anti-pattern explicitly
forbidden in the audit discipline.  The whole point of v0.9 line
16763 — and the deferred-item brief — is that this claim is *open*,
not a citable classical theorem.  Naming an axiom `SAGF_basin_connected`
and concluding from it would be axiom-smuggling.

Instead, we:

1. State `BasinConnectivity` as a `Prop` predicate.
2. State three *independent* sufficient predicates (coercivity,
   at-most-one-local-minimum, Palais–Smale).
3. Prove the conditional theorem `coercive ∧ AtMostOneMin ∧ PS →
   BasinConnectivity` using the **named Palais–Smale closure axiom**
   (cited to Palais–Smale 1964 — Morse theory in Hilbert manifolds).
4. State the Morse counterexample (multiple local minima ⇒
   disconnected sublevel).
5. The verdict: **CONDITIONAL on three predicates whose joint truth
   for `SAGFfunctional` is genuinely open**.

## References

* v0.9 line 16763 — the basin-connectivity claim.
* Bredon, G.E. (1993), *Topology and Geometry*, GTM 139, §III.4.
* Palais, R.S. and Smale, S. (1964), "A generalised Morse theory",
  *Bull. Amer. Math. Soc.* 70, 165–172.
* Morse, M. (1934), *The Calculus of Variations in the Large*,
  AMS Colloquium Publications 18.
-/

noncomputable section

open Set

set_option linter.dupNamespace false

namespace SpectralPhysics.BasinConnectivity

open SpectralPhysics.KSRCompactness

/-! ## The headline open predicate -/

/-- **Basin connectivity** (v0.9 line 16763, open content).

`BasinConnectivity F` says: **every** sublevel set of `F` is
path-connected.  This is the v0.9 "basin is everything"
requirement: the SAGF functional's sublevel structure has no
disconnected components.

This Prop is *not* a theorem in this repository for any specific
`F` arising from the v0.9 framework.  It is the explicit open
content of v0.9.2 deferred §G.3. -/
def BasinConnectivity (F : KSR → ℝ) : Prop :=
  ∀ c : ℝ, IsPathConnected (sublevel F c)

/-- **The v0.9 line 16763 framework claim**, stated as a Prop.

This is the predicate the v0.9 manuscript needs to be true; it is
**not** asserted as a theorem here. -/
def SAGFBasinConnected : Prop := BasinConnectivity SAGFfunctional

/-! ## Trivial closure properties of `BasinConnectivity`

These are honest small facts about the predicate, NOT a closure of
the framework claim. -/

/-- If `F` and `G` agree, their basin-connectivity predicates agree. -/
theorem BasinConnectivity.congr
    {F G : KSR → ℝ} (h : ∀ T, F T = G T) :
    BasinConnectivity F ↔ BasinConnectivity G := by
  unfold BasinConnectivity sublevel
  constructor
  · intro hF c
    have : { T | G T ≤ c } = { T | F T ≤ c } := by
      ext T
      simp [h T]
    rw [this]
    exact hF c
  · intro hG c
    have : { T | F T ≤ c } = { T | G T ≤ c } := by
      ext T
      simp [h T]
    rw [this]
    exact hG c

/-- **Anti-vacuity check**: `BasinConnectivity F` does NOT hold for
the indicator-like functional `F T = if T = KSR.zero then 0 else 1`
when `c = 1` *unless* every sublevel is itself path-connected — i.e.
the predicate has real content and is not satisfied by every `F`.

We state this as a documentation Prop only (proving it requires
exhibiting two non-joinable points; in the discrete topology
shadow this is in principle constructable but distracting). -/
def BasinConnectivity_nonVacuous : Prop :=
  ∃ F : KSR → ℝ, ¬ BasinConnectivity F

end SpectralPhysics.BasinConnectivity

end
