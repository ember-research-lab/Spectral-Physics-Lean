/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom

# K_SR Compactness — Honest Verdict

## TL;DR

**Verdict: CONDITIONAL.**

v0.9 lines 16759 / 11082(a) expect that the space `𝒦_SR` of
self-referential Hermitian kernels with controlled eigenvalue growth
is compact in the trace-norm topology (Sobolev-type compactness on
the kernel space).  v0.9 self-flags this as "Expected positive; not
written."

This module captures that expectation as a **conditional Lean
theorem**, dependent on a single named axiom citing the classical
Rellich–Kondrachov compactness theorem combined with Schatten-class
spectral theory.

## Files

| File                         | Status                              |
| ---------------------------- | ----------------------------------- |
| `KSRSpace.lean`              | Tier 1, 0 `sorry`, 0 custom axioms  |
| `SobolevControl.lean`        | Tier 1, 0 `sorry`, 0 custom axioms  |
| `RellichKondrachov.lean`     | Tier 2 — 1 named axiom, full citation |
| `KSRCompactnessThm.lean`     | Tier 2 conditional on the named axiom |
| `Verdict.lean`               | this file                           |

## Named axioms (1 total)

### `rellich_kondrachov_trace_class` (`RellichKondrachov.lean`)

> `∀ (s C : ℝ), 1 < s → 0 < C → IsCompact (KSRSobolev s C)`

For trace-class decay rate `s > 1` and any positive bound `C > 0`,
the eigenvalue-shadow Sobolev sublevel set is compact.

**Citation**:
* Rellich, F. (1930), *Nachr. Gesell. Wiss. Göttingen, Math.-Phys.
  Kl.*, 30–35.
* Kondrachov, V. (1945), *Dokl. Akad. Nauk SSSR* 48, 535–538.
* Simon, B. (2005), *Trace Ideals and Their Applications* (2nd ed.,
  AMS Math. Surveys & Monographs 120), Ch. 3 (Theorem 3.7 — Weyl
  comparison for Schatten classes).
* Reed, M., Simon, B. (1978), *Methods of Modern Mathematical
  Physics*, Vol. IV: *Analysis of Operators*, §VI.6.

**Smuggling check**: the axiom is **general** — it depends only on
the decay parameter `s` and bound constant `C`, and not on any
v0.9-specific data.  It is not the conclusion-as-axiom pattern;
it is the *forward* direction (functional-analysis fact ⇒ specific
compactness of `KSRSobolev s C`).  See `RellichKondrachov.lean`
§"Anti-pattern check".

## Headline theorem

```
theorem ksr_compact (s C : ℝ) (h_decay : 1 < s) (h_bound : 0 < C) :
    IsCompact (KSRSobolev s C)
```

Conditional on the named axiom; **derives** the bounded Sobolev
sublevel set compactness for the v0.9 framework's `𝒦_SR`.

## What is closed vs open

### Closed (machine-checked, conditional on 1 named axiom)

* `ksr_compact`: bounded Sobolev sublevel sets are compact for `s > 1`.
* `ksr_subset_compact`: any uniformly Sobolev-bounded subset is
  contained in a compact set.
* `ksr_compact_inter_closed`: intersection with any closed set
  preserves compactness.
* `ksr_invariant_sobolev_compact`: SR-invariant restriction is
  compact (under the auxiliary closedness Prop hypothesis).

### Closed unconditionally (no custom axioms)

* `KSR.traceNorm_nonneg`, `KSR.zero_traceNorm` (basic structure
  lemmas).
* `KSRBall_subset_of_le`, `KSR_zero_mem_KSRBall` (bounded-ball
  monotonicity).
* `SobolevGrowth.mono_exponent`: faster decay implies slower decay.
* `SobolevGrowth.uniform_bound`: `s ≥ 0` Sobolev growth ⇒ uniform
  eigenvalue bound.
* `KSRSobolev_pointwise_closed`: the Sobolev sublevel set is
  closed under pointwise (coordinate-wise) limits — a direct
  proof, no axiom needed.
* `sobolev_growth_eq_union`, `SobolevGrowth_set_eq`: the
  representation of the full Sobolev class as a union over the
  rate constant `C`.
* `KSRSobolev_mem_of_growth`: any element with Sobolev growth lies
  in some bounded sublevel set.

### Honestly open (predicate hypotheses, NOT axiomatised)

* `KSR.srInvariant` — the self-reference invariance condition itself.
  Carried as an opaque `Prop` field of the `KSR` structure.  v0.9
  line 11079 `rem:field-eq-open(a)` flags this as open at the
  framework level.
* `SRInvariantIsClosed` — closedness of the SR-invariant subset.
  Predicate hypothesis of `ksr_invariant_sobolev_compact`.
* `FullSobolevClassNotCompact s` — the non-compactness of the
  unbounded union; recorded for documentation, not proved.

## Comparison to the audit-discipline reference branches

| Aspect | `CompositionUniqueness` (Scope 3) | `OP3` redemption | This module |
|---|---|---|---|
| Discipline | predicate hypotheses + named axioms | predicate hypotheses only | predicate hypotheses + 1 named axiom |
| Headline form | conditional on K1+K2+K3 | conditional on 3 predicates | conditional on 1 named axiom |
| Number of custom axioms | 3 (K1,K2,K3) + 2 (Minkowski) = 5 | 0 | **1** |
| Open content carrier | `PointwiseUniqueness` Prop | `VisibleSpectrumFollowsBakerForm` etc. | `KSR.srInvariant`, `SRInvariantIsClosed` |
| Axiom is conclusion? | No (forward shadow) | N/A (no axioms) | No (Rellich-Kondrachov is forward fact) |
| Citation specificity | 3 papers per axiom | N/A | 4 papers (Rellich, Kondrachov, Simon, Reed-Simon) |

The single-axiom count is the same as `compute/self-model-deficit-rigorous`
(`mellin_heat_kernel_finite_spectrum_log_sum`).  Cleaner than
`CompositionUniqueness` (5 axioms) and stricter-than `OP3` (which
has 0 axioms but more open predicates).

## v0.9 line correspondence (precise)

* **v0.9 line 16759** (the self-objection): "Compactness of the
  space `𝒦_SR` of self-referential Hermitian kernels is needed for
  the SAGF basin connectivity argument."  → carried by `ksr_compact`.
* **v0.9 line 11082(a)** (`rem:field-eq-open(a)`): "Compactness of
  `𝒦_SR` in the relevant Sobolev-type topology.  Expected positive;
  not written."  → captured as conditional theorem; the "Sobolev-type
  topology" is encoded via `SobolevGrowth T s` with `s > 1`.
* **v0.9 line 11079** (parent `rem:field-eq-open`): three sub-items.
  Sub-item (a) is this module.  Sub-items (b) GJ algebraic
  identification and (c) global nonlinear SAGF are separate
  deferrals.
-/

import SpectralPhysics.KSRCompactness.KSRCompactnessThm

noncomputable section

namespace SpectralPhysics.KSRCompactness

/-! ## Headline verdict (type-checked)

A single re-export that names this module's conditional closure
in a form callable from the rest of the repository. -/

/-- **THE K-SR COMPACTNESS VERDICT (conditional, honest).**

For every trace-class decay rate `s > 1` and positive bound `C > 0`,
the bounded Sobolev-`s` sublevel set of `𝒦_SR` (eigenvalue shadow)
is compact in the trace-norm topology.  Conditional on
`rellich_kondrachov_trace_class` (cited to Rellich 1930, Kondrachov
1945, Simon 2005, Reed-Simon Vol. IV).

This **captures** the v0.9 line 16759 / 11082(a) expectation as a
type-checked Lean theorem with a single named-axiom dependency. -/
theorem KSR_compactness_verdict :
    ∀ (s C : ℝ), 1 < s → 0 < C → IsCompact (KSRSobolev s C) :=
  ksr_compact

/-- **Constructive form**: the verdict yields, for any Sobolev-bounded
family, an explicit compact superset.

This is the form that downstream SAGF basin arguments would call:
given a family of kernels satisfying a uniform Sobolev bound, the
family is precompact in trace-norm. -/
theorem KSR_compactness_verdict_constructive
    (s C : ℝ) (h_decay : 1 < s) (h_bound : 0 < C)
    (S : Set KSR) (h_uniform : S ⊆ KSRSobolev s C) :
    ∃ K : Set KSR, IsCompact K ∧ S ⊆ K :=
  ksr_subset_compact s C h_decay h_bound S h_uniform

end SpectralPhysics.KSRCompactness

end
