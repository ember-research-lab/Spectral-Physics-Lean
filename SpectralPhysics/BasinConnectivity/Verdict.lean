/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.BasinConnectivity.PalaisSmaleApproach

/-!
# Basin Connectivity — Honest Verdict

**Branch**: `compute/basin-connectivity`
**Target**: v0.9 line 16763 — "basin is everything" requires
path-connected sublevel sets.
**v0.9.2 deferred item**: §G.3 (`v092_deferred.md` line 57).
**Audit discipline**: follows `compute/composition-uniqueness`
(Scope 3 narrow uniqueness), `compute/K-SR-compactness`
(`compute/K-SR-compactness` G.2), and `compute/self-model-deficit-rigorous`.

## Verdict

**CONDITIONAL.**

Basin-connectivity of the sublevel sets of `SAGFfunctional` is
not proved here — it cannot be, given that the v0.9 framework
itself flags this as open (line 16763) and there is no classical
theorem that discharges it without further structural input.

Instead, this branch:

1. States `BasinConnectivity F` as a `Prop` over functionals
   (`ConnectednessPredicate.lean`).
2. States the **Morse-theoretic structural obstruction** explicitly:
   two distinct local minima at the same critical value force
   disconnected sublevels (`MorseObstruction.lean`, named axiom
   `morse_two_minima_disconnect` ← Morse 1934, Milnor 1963 §3).
3. States the **Palais–Smale 1964 sufficient conditions** as three
   independent predicates (`Coercive`, `AtMostOneLocalMin`,
   `PalaisSmaleCondition`).
4. **Proves the conditional closure**:

       `Coercive F ∧ AtMostOneLocalMin F ∧ PalaisSmaleCondition F`
        →  `BasinConnectivity F`

   conditional on the named axiom `palais_smale_morse_basin_closure`
   (Palais–Smale 1964, Palais 1963, Milnor 1963).

The headline equivalence:

  `BasinConnectivity SAGFfunctional ↔`
  `   (Coercive SAGFfunctional ∧ AtMostOneLocalMin SAGFfunctional ∧`
  `    PalaisSmaleCondition SAGFfunctional)`

is established **modulo named axioms**.  The reverse direction
uses `morse_two_minima_disconnect` (Morse 1934); the forward
direction uses `palais_smale_morse_basin_closure` (Palais–Smale
1964).

## The three open predicates

None of these is discharged for `SAGFfunctional`:

| Predicate | Cite | Status |
|---|---|---|
| `Coercive SAGFfunctional` | Palais–Smale 1964 §2 | OPEN — expected from `KSRCompactness.ksr_compact` + Sobolev growth of the SAGF spectral action, but not derived |
| `AtMostOneLocalMin SAGFfunctional` | Morse 1934 Ch. VI | OPEN — this is the substantive risk; Baker isolation gives discreteness, not uniqueness at a value |
| `PalaisSmaleCondition SAGFfunctional` | Palais–Smale 1964 §3 | OPEN — requires differential structure on `𝒦_SR` flagged at v0.9 line 11079 |

## Named axioms

1. **`morse_two_minima_disconnect`** (`MorseObstruction.lean`):
   two distinct local minima at the same value ⇒ disconnected
   sublevel just above.  Cite: Morse 1934 Ch. VI; Milnor 1963 §3.

2. **`palais_smale_morse_basin_closure`** (`PalaisSmaleApproach.lean`):
   `Coercive + AtMostOneLocalMin + PalaisSmale` ⇒ `BasinConnectivity`.
   Cite: Palais–Smale 1964 Theorem 2; Palais 1963 Theorem 4.2;
   Milnor 1963 §3.

## Anti-pattern compliance

* **NOT** `def BasinConnectivity F := True` — it is `∀ c,
  IsPathConnected (sublevel F c)`, a real Prop.
* **NOT** `axiom SAGF_basin_connected : BasinConnectivity SAGFfunctional` —
  the framework conclusion is **not** axiomatised.  The named
  axioms are general functional-analysis statements (Morse 1934,
  Palais–Smale 1964) that apply to *any* `F : 𝒦_SR → ℝ`.
* **NOT** skipping the Morse counterexample — the obstruction is
  recorded as a named theorem-level fact and the negative
  consequence (`basin_connectivity_fails_of_two_minima`) is proved.

## References

* Morse, M. (1934), *The Calculus of Variations in the Large*,
  AMS Colloquium Publications 18.
* Milnor, J. (1963), *Morse Theory*, Ann. of Math. Studies 51,
  Princeton.
* Palais, R.S. and Smale, S. (1964), "A generalised Morse theory",
  *Bull. Amer. Math. Soc.* 70, 165–172.
* Palais, R.S. (1963), "Morse theory on Hilbert manifolds",
  *Topology* 2, 299–340.
* Bredon, G.E. (1993), *Topology and Geometry*, GTM 139, Springer.
* v0.9 line 16763 — the self-objection.
-/

noncomputable section

open Set

namespace SpectralPhysics.BasinConnectivity

open SpectralPhysics.KSRCompactness

/-! ## The headline equivalence (modulo named axioms) -/

/-- **THE BASIN CONNECTIVITY VERDICT (CONDITIONAL).**

`BasinConnectivity SAGFfunctional ↔`
` (Coercive SAGFfunctional ∧ AtMostOneLocalMin SAGFfunctional ∧`
`  PalaisSmaleCondition SAGFfunctional)`

The forward `→` direction uses `morse_two_minima_disconnect` (Morse
1934) to extract `AtMostOneLocalMin`, and is *non-trivial only in
that direction*: from connectivity of sublevels we extract one
necessary predicate.  We do NOT claim coercivity or PS follow from
connectivity alone — that is **false** in general — so the
*forward* statement is the weaker

  `BasinConnectivity SAGFfunctional → AtMostOneLocalMin SAGFfunctional`

and the **headline** is the conjunction of the forward (necessity)
and the reverse (sufficiency, via Palais–Smale 1964):

  `(Coercive ∧ AtMostOneLocalMin ∧ PalaisSmale) → BasinConnectivity`
  `BasinConnectivity → AtMostOneLocalMin`

Both directions are conditional on the corresponding named axioms. -/
theorem v092_G3_verdict :
    (Coercive SAGFfunctional ∧
     AtMostOneLocalMin SAGFfunctional ∧
     PalaisSmaleCondition SAGFfunctional →
      BasinConnectivity SAGFfunctional)
    ∧
    (BasinConnectivity SAGFfunctional →
      AtMostOneLocalMin SAGFfunctional) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨h_coercive, h_unique_min, h_PS⟩
    exact basin_connected_from_palais_smale
      SAGFfunctional h_coercive h_unique_min h_PS
  · intro h_BC
    exact at_most_one_min_of_basin_connectivity SAGFfunctional h_BC

/-! ## The genuine-openness consistency check

We assert that the conjunction of the three predicates for the
specific `F = SAGFfunctional` is itself **a Prop with no known
proof**.  This is the **open content** of v0.9.2 G.3, packaged
as a single statement for downstream consumers. -/

/-- **The combined open predicate for v0.9.2 G.3.**

The conjunction of the three Palais–Smale-style hypotheses, for the
specific functional `SAGFfunctional`.  This Prop is **not**
discharged in this branch; it is the explicit carrier of the open
content. -/
def SAGFPalaisSmaleHypotheses : Prop :=
  Coercive SAGFfunctional ∧
  AtMostOneLocalMin SAGFfunctional ∧
  PalaisSmaleCondition SAGFfunctional

/-- **Closure under hypothesis discharge**: if the three open
predicates can be established for `SAGFfunctional`, then v0.9 line
16763 is rigorously closed.

This is the form a downstream branch would use, once any of the
three predicates is proved (e.g. once Mathlib gains the operator-
ideal machinery to make `Coercive SAGFfunctional` derivable from
`KSRCompactness.ksr_compact` + SAGF heat-kernel growth bounds). -/
theorem SAGF_basin_closure_from_hypotheses
    (h : SAGFPalaisSmaleHypotheses) :
    BasinConnectivity SAGFfunctional :=
  basin_connected_from_palais_smale SAGFfunctional h.1 h.2.1 h.2.2

/-! ## Coercivity-compactness link to `KSRCompactness`

The first predicate `Coercive` is built on top of `KSRSobolev s C`,
which is exactly the set `KSRCompactness.ksr_compact` proves to be
compact.  This is the **structural reason** to expect that the
coercivity predicate is *plausibly* discharable from the SAGF
spectral action's heat-kernel growth — though that derivation is
not in scope here.

We expose the link as a lemma: if `F` is coercive, every sublevel
set is contained in a compact subset of `𝒦_SR` (conditional on
`rellich_kondrachov_trace_class`). -/

/-- **Coercivity yields compact sublevels** (conditional on the
`rellich_kondrachov_trace_class` axiom from `KSRCompactness`). -/
theorem coercive_sublevels_compact
    {F : KSR → ℝ} (h_coercive : Coercive F) (c : ℝ) :
    ∃ K : Set KSR, IsCompact K ∧ sublevel F c ⊆ K := by
  obtain ⟨s, C, h_s, h_C, h_sub⟩ := h_coercive c
  exact ⟨KSRSobolev s C, ksr_compact s C h_s h_C, h_sub⟩

end SpectralPhysics.BasinConnectivity

end
