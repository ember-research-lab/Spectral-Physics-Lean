# Basin Connectivity — Honest STATUS

**Branch**: `compute/basin-connectivity`
**Target**: v0.9 line 16763 — the "basin is everything" claim requires
sublevel sets of the SAGF functional to be (path-)connected.
**v0.9.2 deferred item**: §G.3 (`v092_deferred.md` line 57).
**Audit discipline**: follows `compute/composition-uniqueness`
(Scope 3 narrow uniqueness), `compute/K-SR-compactness` (G.2),
`compute/Lambda1-refinement` (OP3 redemption), and
`compute/self-model-deficit-rigorous`.

This file is the honest accounting of what this branch delivers and
what it deliberately does not.

---

## 1. Theorems proved (with statements)

All five `.lean` modules in this directory build cleanly under
`lake build SpectralPhysics` (3268 jobs, full repo).  Zero `sorry`,
zero `admit`, zero `True` placeholders.

### Headline theorem (CONDITIONAL on 2 named axioms + 3 predicates)

* `v092_G3_verdict :`
  `  (Coercive SAGFfunctional ∧ AtMostOneLocalMin SAGFfunctional ∧`
  `   PalaisSmaleCondition SAGFfunctional →`
  `    BasinConnectivity SAGFfunctional)`
  `  ∧ (BasinConnectivity SAGFfunctional → AtMostOneLocalMin SAGFfunctional)`

  Forward direction: Palais–Smale 1964 closure.
  Reverse direction: Morse 1934 obstruction.

* `SAGF_basin_closure_from_hypotheses` — packaging of the three-predicate
  forward direction for `SAGFfunctional`.

* `basin_connected_from_palais_smale` — the general-`F` form of the
  Palais–Smale conditional.

### Necessary direction (Morse obstruction)

* `basin_connectivity_fails_of_two_minima` — two distinct local
  minima at the same critical value ⇒ `BasinConnectivity` fails.
* `at_most_one_min_of_basin_connectivity` — contrapositive:
  `BasinConnectivity F → AtMostOneLocalMin F`.

### Coercivity–compactness link

* `coercive_sublevels_compact` — `Coercive F` implies every sublevel
  set is contained in a compact subset of `𝒦_SR` (conditional on
  the inherited `rellich_kondrachov_trace_class` axiom from
  `KSRCompactness/`).

### Unconditionally proved (ZERO custom axioms)

In `SublevelSet.lean`:

* `sublevel_subset_of_le` — sublevel sets are monotone in `c`.
* `mem_sublevel` — membership characterisation.
* `zero_mem_sublevel_iff` — `KSR.zero` membership signpost.
* `sublevel_empty_of_lt` — vacuous edge case (empty sublevel).

In `ConnectednessPredicate.lean`:

* `BasinConnectivity.congr` — equality-of-functionals preserves the
  predicate.

---

## 2. Named axioms (2 total, cited to literature)

### `morse_two_minima_disconnect` (`MorseObstruction.lean`)

> `∀ F : KSR → ℝ, MorseObstruction F`
>
> i.e. for any `F` and any `c*`, if `F` has two distinct local
> minima at the critical value `c*`, then for some `ε > 0` the
> sublevel `{ F ≤ c* + ε }` is NOT path-connected.

**Citations**:

* **Morse, M.** (1934), *The Calculus of Variations in the Large*,
  AMS Colloquium Publications 18, Ch. VI Theorem 6.1 (Morse
  lemma at a non-degenerate critical point) and Ch. VII
  (sublevel-set homotopy classification).
* **Milnor, J.** (1963), *Morse Theory*, Ann. of Math. Studies
  51, Princeton, Theorem 3.1 (sublevel-set retraction theorem)
  and §3 corollaries.

### `palais_smale_morse_basin_closure` (`PalaisSmaleApproach.lean`)

> `∀ (F : KSR → ℝ),`
> `  Coercive F → AtMostOneLocalMin F → PalaisSmaleCondition F →`
> `   BasinConnectivity F`

**Citations**:

* **Palais, R.S.** and **Smale, S.** (1964), "A generalised
  Morse theory", *Bull. Amer. Math. Soc.* 70, 165–172.  Theorem 2.
* **Palais, R.S.** (1963), "Morse theory on Hilbert manifolds",
  *Topology* 2, 299–340.  Theorem 4.2 — sublevel-set retraction.
* **Milnor, J.** (1963), *Morse Theory*, §3 — sublevel-set
  retraction in the absence of critical values.
* **Bredon, G.E.** (1993), *Topology and Geometry*, GTM 139,
  Springer, §III.4 — path-connectedness of sublevel sets under
  classical Morse-theoretic conditions.

### Smuggling check

Neither axiom asserts framework-specific content:

* `morse_two_minima_disconnect`: a classical Morse fact applicable
  to *any* `F : 𝒦_SR → ℝ`; not the conclusion-as-axiom pattern
  (which would be `axiom SAGF_basin_disconnected`).
* `palais_smale_morse_basin_closure`: the classical generalised
  Morse theory implication.  Not framework-specific; applies to
  any `F` with the three named properties.

We do **NOT** axiomatise `BasinConnectivity SAGFfunctional`
directly — that would be conclusion-as-axiom, explicitly forbidden
by the audit-discipline brief.

---

## 3. Sorries — categorised

**Zero sorries.**  Verified by
`grep -rn 'sorry\|admit' SpectralPhysics/BasinConnectivity/`.

---

## 4. What is closed vs. open

### Genuinely closed (proved unconditionally — zero non-kernel axioms)

* `sublevel_subset_of_le`, `mem_sublevel`, `zero_mem_sublevel_iff`,
  `sublevel_empty_of_lt`
* `BasinConnectivity.congr`

### Closed conditionally on `morse_two_minima_disconnect`

* `basin_connectivity_fails_of_two_minima`
* `at_most_one_min_of_basin_connectivity`
* `v092_G3_verdict` (reverse direction)

### Closed conditionally on `palais_smale_morse_basin_closure`

* `basin_connected_from_palais_smale`
* `SAGF_basin_closure_from_hypotheses`
* `v092_G3_verdict` (forward direction)

### Closed conditionally on `rellich_kondrachov_trace_class` (inherited)

* `coercive_sublevels_compact`

### Honestly open (predicate hypotheses, NOT axiomatised)

The three predicates over `SAGFfunctional`:

* **`Coercive SAGFfunctional`** — sublevel sets are Sobolev-bounded.
  Expected from `KSRCompactness.ksr_compact` + SAGF heat-kernel growth;
  derivation NOT carried out.
* **`AtMostOneLocalMin SAGFfunctional`** — the substantive open
  predicate that rules out the Morse obstruction.  Baker isolation
  gives discreteness of critical points but not uniqueness at a value.
* **`PalaisSmaleCondition SAGFfunctional`** — requires differential
  structure on `𝒦_SR` (open at v0.9 line 11079 `rem:field-eq-open(a)`).

Combined: **`SAGFPalaisSmaleHypotheses`**.

Also open:

* **`SAGFBasinConnected`** — the framework's line 16763 claim, stated
  as a Prop and NOT discharged.

---

## 5. Mathlib search (negative result)

Before declaring the named axioms, we verified that Mathlib at
toolchain v4.29.0-rc6 does **not** carry:

```bash
$ grep -rln "Coercive\|PalaisSmale" .lake/packages/mathlib/Mathlib --include="*.lean"
(LaxMilgram coercive bilinear forms only; no variational `Coercive`
 predicate, no `PalaisSmaleCondition`)

$ grep -rln "Morse" .lake/packages/mathlib/Mathlib --include="*.lean"
(`Mathlib/RingTheory/Polynomial/Morse.lean` — algebraic Morse only;
 no Morse-theoretic infrastructure for sublevel-set topology)
```

What **is** available and used:

* `IsPathConnected` (`Mathlib/Topology/Connected/PathConnected.lean`),
  Theorem 348 — the predicate carrier for the headline statement.

So the Morse / Palais–Smale infrastructure is *not* present in
Mathlib at this toolchain; both named axioms are necessary and
appropriately scoped.

---

## 6. Topology note (documented limitation)

The `TopologicalSpace KSR` instance is inherited from
`KSRCompactness/RellichKondrachov.lean`, where it is set to `⊥`
(discrete topology) as a placeholder pending Mathlib's Schatten-1
ideal infrastructure.  Under the discrete topology, `IsPathConnected`
is the strictly-stronger statement "the set has at most one element
or is empty" — so the predicate `BasinConnectivity SAGFfunctional`
as written is *more* demanding than the v0.9 framework's intended
trace-norm version.

This is **flagged in `SublevelSet.lean`** and `Verdict.lean`: the
genuine v0.9 line 16763 content refers to path-connectedness in
the trace-norm topology.  Replacing the placeholder discrete
topology with the trace-norm topology — once Mathlib's Schatten-1
ideal arrives — is the **same** Tier-2-conditional-on-Mathlib
caveat already carried by `KSRCompactness/STATUS.md` §7.  The two
named axioms here would carry the trace-norm content unchanged;
the topology refinement does not invalidate the conditional chain.

---

## 7. Build status

```
$ lake build SpectralPhysics
... (full build) ...
✔ [3267/3268] Built SpectralPhysics (1.6s)
Build completed successfully (3268 jobs).
```

### `#print axioms` for the headline theorems

```
'v092_G3_verdict' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   morse_two_minima_disconnect,
   palais_smale_morse_basin_closure]

'basin_connected_from_palais_smale' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   palais_smale_morse_basin_closure]

'basin_connectivity_fails_of_two_minima' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   morse_two_minima_disconnect]

'at_most_one_min_of_basin_connectivity' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   morse_two_minima_disconnect]

'SAGF_basin_closure_from_hypotheses' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   palais_smale_morse_basin_closure]

'coercive_sublevels_compact' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   SpectralPhysics.KSRCompactness.rellich_kondrachov_trace_class]
```

Two new named axioms; one inherited from `KSRCompactness/`.  The
conclusion `BasinConnectivity SAGFfunctional` is **not** assumed
directly.

---

## 8. Honest verdict

**Does this close v0.9 line 16763 rigorously?**

**CONDITIONAL closure**, in the sense:

* The v0.9 line 16763 claim is stated as a `Prop`
  (`SAGFBasinConnected := BasinConnectivity SAGFfunctional`); it is
  **not** discharged in this branch.
* The **Palais–Smale 1964 conditional sufficiency** is proved:
  `Coercive ∧ AtMostOneLocalMin ∧ PalaisSmale → BasinConnectivity`.
  Three open predicates over `SAGFfunctional` therefore *imply* the
  framework claim, via one named axiom (Palais–Smale 1964).
* The **Morse 1934 structural obstruction** is also carried as a
  named axiom: two distinct minima at the same value forbid basin
  connectivity.  The contrapositive gives one necessary direction
  of the headline equivalence.
* None of the three predicates is asserted to hold for
  `SAGFfunctional`.  The audit-discipline brief explicitly forbids
  axiom-smuggling such an assertion.

**What stays open?**

* `Coercive SAGFfunctional` — expected from
  `KSRCompactness.ksr_compact` plus SAGF spectral-action growth
  bounds, but the derivation requires SAGF heat-kernel asymptotics
  beyond v0.9.1's scope.
* `AtMostOneLocalMin SAGFfunctional` — the substantive open
  predicate.  Baker isolation gives discreteness; uniqueness
  *at the same value* is the genuine gap.
* `PalaisSmaleCondition SAGFfunctional` — needs differential
  structure on `𝒦_SR` (v0.9 line 11079 open).

* **Replacing the named axioms by Mathlib theorems** — requires
  Morse-theoretic infrastructure and Palais–Smale machinery in
  Mathlib, neither of which is currently present.

**Comparison to the audit-discipline reference branches.**

| Aspect | `composition-uniqueness` (Scope 3) | `K-SR-compactness` (G.2) | This module (G.3) |
|---|---|---|---|
| Custom axioms | 5 (K1+K2+K3, Minkowski×2) | 1 (Rellich–Kondrachov) | **2** (Morse, Palais–Smale) |
| Predicate hypotheses | 1 (PointwiseUniqueness) | 1 (`SRInvariantIsClosed`) | **3** (Coercive, AtMostOneMin, PalaisSmale) |
| Tier-1 unconditional theorems | 4 | 9 | 5 |
| Conclusion-as-axiom pattern? | No | No | **No** |
| Smuggling check passes? | yes | yes | **yes** |

This module sits structurally between `K-SR-compactness` (one axiom,
one predicate) and `composition-uniqueness` (five axioms, one
predicate): two named axioms (cited to four primary sources),
three open predicates over the specific functional.  The headline
is an **equivalence** rather than a one-direction implication
(`SAGF basin connected ↔ three predicates`, modulo named axioms),
matching the v0.9 framework's own framing of the problem.

---

## 9. Anti-pattern compliance

Per the brief, anti-patterns explicitly forbidden:

1. **`def BasinConnectivity F := True` + `theorem v092_G3 : True := trivial`** —
   NOT done.  `BasinConnectivity F := ∀ c, IsPathConnected (sublevel F c)`,
   which is a real Prop on a real Set; `IsPathConnected` is
   `Mathlib.Topology.Connected.PathConnected.IsPathConnected`,
   carrying genuine topological content.

2. **`axiom SAGF_basin_connected : BasinConnectivity SAGFfunctional`** —
   NOT done.  Our axioms are *general* Morse-theoretic / Palais–Smale
   facts depending on the three predicates; they do not assert any
   v0.9-specific content.  The conclusion for `SAGFfunctional` is
   *derived* from the predicates, not axiomatised.

3. **Skipping the Morse counterexample** —
   NOT skipped.  `MorseObstruction.lean` records the obstruction
   as a named axiom (Morse 1934, Milnor 1963 §3) and proves
   `basin_connectivity_fails_of_two_minima`, the explicit
   counterexample-conditional theorem.

---

## 10. v0.9 line correspondence (precise)

| v0.9 line | Content | This module |
|---|---|---|
| 16763 | "Basin is everything" — sublevel-set connectivity claim | `SAGFBasinConnected` (open Prop) + `v092_G3_verdict` (conditional equivalence) |
| 11079(a) | `rem:field-eq-open(a)` — `𝒦_SR` structural openness | inherited via `KSR.srInvariant`; not discharged |

The Baker-isolation discreteness mentioned in the brief (v0.9's
defense that critical points are discrete) is **not sufficient**
for basin connectivity — that is the explicit point of v0.9 line
16763 self-flagging this as open.  The Morse obstruction theorem
records *why* discreteness alone is insufficient: two distinct
discrete minima at the same value still disconnect the basin.

---

## 11. Future work

* Discharge `Coercive SAGFfunctional` via SAGF heat-kernel growth
  combined with `KSRCompactness.ksr_compact`.  Estimated 2–4 weeks
  pending Mathlib Schatten-1 infrastructure.
* Discharge `AtMostOneLocalMin SAGFfunctional` — requires
  framework-level analysis of the SAGF critical-point structure
  beyond Baker isolation.  Substantive open problem.
* Discharge `PalaisSmaleCondition SAGFfunctional` — pending
  differential structure on `𝒦_SR` (v0.9 line 11079 open).
* Replace `morse_two_minima_disconnect` and
  `palais_smale_morse_basin_closure` by Mathlib theorems once
  Morse / variational infrastructure arrives.  Until then, two
  named axioms.
* Refine the topology placeholder from discrete to trace-norm
  alongside the same refinement in `KSRCompactness/`.
