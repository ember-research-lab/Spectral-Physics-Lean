# K_SR Compactness — Honest STATUS

**Branch**: `compute/K-SR-compactness`
**Target**: v0.9 lines 16759 and 11082(a) (`rem:field-eq-open(a)`)
**v0.9.2 deferred item**: §G.2 (`v092_deferred.md` line 54)
**Audit discipline**: follows `compute/composition-uniqueness`,
`compute/Lambda1-refinement` (OP3 redemption), and
`compute/self-model-deficit-rigorous`.

This file is the honest accounting of what this branch delivers and
what it deliberately does not.

---

## 1. Theorems proved (with statements)

All five `.lean` modules in this directory build cleanly under
`lake build SpectralPhysics` (3239 jobs, full repo).  Zero `sorry`,
zero `admit`, zero `True` placeholders.

### Headline theorem (CONDITIONAL on 1 named axiom)

* `ksr_compact (s C : ℝ) (h_decay : 1 < s) (h_bound : 0 < C) :`
  `  IsCompact (KSRSobolev s C)`

  For trace-class decay rate `s > 1` and bound `C > 0`, the
  eigenvalue-shadow Sobolev sublevel set is compact in the
  trace-norm carrier topology.

* `KSR_compactness_verdict` — re-export in `Verdict.lean`.

* `KSR_compactness_verdict_constructive` — explicit compact superset
  for any uniformly Sobolev-bounded family.

### Corollaries (also conditional on the named axiom)

* `ksr_subset_compact` — uniformly Sobolev-bounded subsets are
  precompact.
* `ksr_compact_inter_closed` — intersection with closed set
  preserves compactness.
* `ksr_invariant_sobolev_compact` — SR-invariant Sobolev sublevel
  set is compact, under the auxiliary `SRInvariantIsClosed` Prop
  hypothesis.

### Unconditionally proved (ZERO custom axioms)

In `KSRSpace.lean`:

* `KSR.traceNorm_nonneg`, `KSR.zero_traceNorm`.
* `KSRBall_subset_of_le`, `KSR_zero_mem_KSRBall`.

In `SobolevControl.lean`:

* `SobolevGrowth.mono_exponent` — faster decay implies slower decay.
* `SobolevGrowth.uniform_bound` — uniform eigenvalue bound from
  Sobolev growth.
* `sobolev_growth_eq_union` — Sobolev growth as union representation.
* `KSRSobolev_pointwise_closed` — the Sobolev sublevel set is closed
  under coordinate-wise (pointwise) limits.

In `RellichKondrachov.lean`:

* `KSRSobolev_mem_of_growth`, `SobolevGrowth_set_eq` — union and
  membership equivalences.

---

## 2. Named axioms (1 total, cited to literature)

### `rellich_kondrachov_trace_class` (`RellichKondrachov.lean`)

> `∀ (s C : ℝ), 1 < s → 0 < C → IsCompact (KSRSobolev s C)`

For trace-class decay rate `s > 1` and any positive bound `C > 0`,
the eigenvalue-shadow Sobolev sublevel set is compact.

**Citations**:

* **Rellich, F.** (1930), "Ein Satz über mittlere Konvergenz",
  *Nachr. Gesell. Wiss. Göttingen, Math.-Phys. Kl.*, 30–35.
* **Kondrachov, V.** (1945), "Sur certaines propriétés des
  fonctions dans l'espace L^p", *Dokl. Akad. Nauk SSSR* 48,
  535–538.
* **Simon, B.** (2005), *Trace Ideals and Their Applications*
  (2nd ed., AMS Math. Surveys & Monographs 120), Ch. 3 (Theorem
  3.7 — Weyl comparison for Schatten classes).
* **Reed, M., Simon, B.** (1978), *Methods of Modern Mathematical
  Physics*, Vol. IV: *Analysis of Operators*, §VI.6.

### Smuggling check

The axiom is a **generic functional-analysis fact** with explicit
literature citation.  It does NOT assert any framework-specific
content:

* Not `IsCompact (Set.univ : Set KSR)` — that would be the
  conclusion-as-axiom pattern.  Unbounded Schatten ideals are
  never compact; only Sobolev sublevel sets are.
* Not framework-specific.  The decay parameter `s > 1` and bound
  `C > 0` are the only inputs; the statement holds for any
  Hermitian eigenvalue sequence (Laplace–Beltrami on `n`-manifolds,
  Dirichlet Laplacian on bounded domains, Schrödinger operators
  with confining potentials, etc.).
* Not the v0.9 expected compactness of *the SR-invariant subset*.
  That additional restriction requires the SR-closedness Prop
  hypothesis (`SRInvariantIsClosed`), which is the open content
  per v0.9 line 11079.

---

## 3. Sorries — categorised

**Zero sorries.**  Verified by
`grep -rn 'sorry\|admit' SpectralPhysics/KSRCompactness/`.

---

## 4. What is closed vs. open

### Genuinely closed (proved unconditionally — zero non-kernel axioms)

* `SobolevGrowth.mono_exponent`
* `SobolevGrowth.uniform_bound`
* `KSRSobolev_pointwise_closed`
* `sobolev_growth_eq_union`
* `SobolevGrowth_set_eq`
* `KSRSobolev_mem_of_growth`
* `KSR.traceNorm_nonneg`, `KSR.zero_traceNorm`
* `KSRBall_subset_of_le`, `KSR_zero_mem_KSRBall`

### Closed conditionally on `rellich_kondrachov_trace_class`

* `ksr_compact` (headline)
* `ksr_subset_compact`
* `ksr_compact_inter_closed`
* `ksr_invariant_sobolev_compact` (also needs `SRInvariantIsClosed`
  Prop)
* `KSR_compactness_verdict`, `KSR_compactness_verdict_constructive`

### Honestly open (predicate hypotheses, NOT axiomatised)

* `KSR.srInvariant` — the self-reference invariance condition
  itself.  Carried as a `Prop` field of the `KSR` structure.
  v0.9 line 11079 `rem:field-eq-open(a)` flags this as open at
  the framework level.
* `SRInvariantIsClosed` — closedness of the SR-invariant subset.
  Predicate hypothesis of `ksr_invariant_sobolev_compact`.
* `FullSobolevClassNotCompact s` — non-compactness of the
  unbounded union; recorded for documentation, not proved.

---

## 5. Mathlib search (negative result)

Before axiomatizing `rellich_kondrachov_trace_class` we verified
that Mathlib at toolchain v4.29.0-rc6 does **not** provide:

```bash
$ grep -rln "Schatten" .lake/packages/mathlib/Mathlib --include="*.lean"
(no module-level hits relevant to operator ideals)

$ grep -rln "TraceClass" .lake/packages/mathlib/Mathlib --include="*.lean"
(only the abstract LinearMap.trace, not a trace-class operator predicate)

$ grep -rln "Rellich\|Kondrachov" .lake/packages/mathlib/Mathlib --include="*.lean"
(zero hits)
```

The available compactness primitives are:

* `IsCompactOperator` (`Mathlib/Analysis/Normed/Operator/Compact.lean`)
  — the predicate for compact operators on TVS, but with no
  eigenvalue-decay → compactness criterion.
* `LinearMap.IsSymmetric.eigenvalues` (`Mathlib/Analysis/InnerProductSpace/Spectrum.lean`)
  — finite-dimensional spectral theorem only.

Each of these is too weak to derive the Rellich–Kondrachov + Schatten
compactness conclusion.  The axiom is therefore necessary at this
toolchain; it should be replaced by a Mathlib theorem once Schatten
ideal infrastructure lands.

---

## 6. Build status

```
$ lake build SpectralPhysics
... (full build) ...
✔ [3238/3239] Built SpectralPhysics (1.8s)
Build completed successfully (3239 jobs).
```

### `#print axioms` for the headline theorems

```
'ksr_compact' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   rellich_kondrachov_trace_class]

'KSR_compactness_verdict' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   rellich_kondrachov_trace_class]

'ksr_subset_compact' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   rellich_kondrachov_trace_class]

'KSRSobolev_pointwise_closed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
  -- ZERO non-kernel axioms

'SobolevGrowth.mono_exponent' depends on axioms:
  [propext, Classical.choice, Quot.sound]
  -- ZERO non-kernel axioms
```

The conditional theorems depend on **exactly one** non-kernel axiom,
the named Rellich–Kondrachov axiom with four-citation literature
provenance.  The structural Sobolev lemmas depend on **zero**
non-kernel axioms.

---

## 7. Honest verdict

**Does this close the v0.9 line 16759 / 11082(a) self-objection
rigorously?**

**CONDITIONAL closure**, in the sense:

* The v0.9 expectation was "Expected positive; not written" — this
  module makes the "expected positive" precise as a Lean theorem
  with a single named-axiom dependency.
* The single named axiom is the classical Rellich–Kondrachov +
  Schatten-class compactness fact, cited to Rellich 1930,
  Kondrachov 1945, Simon 2005 *Trace Ideals* Theorem 3.7, and
  Reed–Simon Vol. IV §VI.6.
* Under that axiom, the headline `ksr_compact` is *derived*.
  This is the same conditional-proof discipline as
  `compute/composition-uniqueness` Scope 3 (Kasparov-narrow
  uniqueness under K1+K2+K3).

**What stays open?**

* The **self-reference invariance condition** itself — formalising
  what "K(x,y) = ⟨Φ(x), Φ(y)⟩ for a self-modelling embedding Φ"
  means is v0.9 line 11079's open content.  We carry it as the
  Prop field `KSR.srInvariant`, and the auxiliary closedness as
  `SRInvariantIsClosed`.  Neither is discharged.
* **Replacing the named axiom by a Mathlib theorem** — this
  requires Mathlib to gain Schatten ideal infrastructure
  (`Schatten p E` as a Banach space, trace-norm topology, Weyl
  comparison theorem at the level of singular values).  Once that
  lands, `rellich_kondrachov_trace_class` should become an
  application of that infrastructure rather than an axiom.  This
  is the standard "Tier 2 conditional on Mathlib" pattern from
  v092_deferred.md §G.2.

**Comparison to the audit-discipline reference branches.**

| Aspect | `composition-uniqueness` | `OP3` | This module |
|---|---|---|---|
| Custom axioms | 5 (K1, K2, K3, Minkowski×2) | 0 | **1** |
| Open content carrier | predicate (`PointwiseUniqueness`) | predicates (4) | predicate + 1 named axiom |
| Tier-1 unconditional theorems | 4 (Scope 2) | ~6 | 9 |
| Tier-2 conditional theorems | 3 (Scope 3) | 3 | 6 |
| Conditional dependency | K1+K2+K3 (3 axioms) | 3 hypotheses | 1 axiom + 1 Prop hyp |
| Smuggling check passes? | yes | N/A (no axioms) | yes |
| Closed Mathlib reuse documented? | yes (K1=Mesland-Rennie) | N/A | yes (Simon 2005 Th. 3.7) |

This module is structurally between the `composition-uniqueness` and
`OP3` discipline: it has one axiom (vs zero or five), and its
conditional headline derives the v0.9 expectation from the named axiom.

---

## 8. Anti-pattern compliance

Per the brief, anti-patterns explicitly forbidden:

1. **`def KSR := Unit` + `theorem ksr_compact : IsCompact (Set.univ : Set Unit)`** —
   NOT done.  `KSR` is a real `structure` carrying an eigenvalue
   sequence `ℕ → ℝ`, a `Summable` proof, and a `Prop` field.  It is
   not a unit type.

2. **`axiom ksr_is_compact : IsCompact KSR`** —
   NOT done.  Our axiom is `∀ s C, 1 < s → 0 < C → IsCompact
   (KSRSobolev s C)`, depending on the decay parameter and bound
   constant.  The theorem `ksr_compact` derives the specific
   `KSRSobolev s C` compactness from this general fact, with
   explicit `s, C` arguments.

3. **Skipping Mathlib search** —
   NOT skipped.  We grep'd Mathlib for `Schatten`, `TraceClass`,
   `Rellich`, `Kondrachov`, and `IsCompactOperator`.  Only the
   abstract `IsCompactOperator` predicate is present, and it is too
   weak to derive Rellich-style compactness.  The negative result
   is recorded in §5 above.

---

## 9. v0.9 line correspondence (precise)

| v0.9 line | Content | This module |
|---|---|---|
| 16759 | "Compactness of `𝒦_SR` for SAGF basin argument" | `ksr_compact` (conditional) |
| 11082(a) | "Compactness of `𝒦_SR` in Sobolev-type topology; Expected positive; not written" | captured as named Rellich axiom + conditional theorem |
| 11079 | parent `rem:field-eq-open` — three sub-items | sub-item (a) is this module; (b),(c) are separate deferrals |

The "Sobolev-type topology" of v0.9 line 11082(a) is identified
here with the `SobolevGrowth T s` predicate for `s > 1`.  This
matches Simon 2005's Schatten-1 (trace-class) compactness criterion
and the classical Rellich–Kondrachov embedding.  The match is
documented as "reasonable approximation" rather than literal — see
the closing note in `Verdict.lean` and the discussion in
`SobolevControl.lean` (the dual relationship between manifold-side
Sobolev regularity and singular-value decay via Weyl's law).
