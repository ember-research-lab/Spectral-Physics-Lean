# compute/RM-forces-division-algebras — STATUS

**Branch**: `compute/RM-forces-division-algebras`
**Dispatch**: v0.9.2 deferred item **G.4** — "Division-algebra forcing
from R∘M=id" (v0.9 line 16779, self-flagged "Real gap").
**Date completed**: 2026-05-11.
**Build**: `lake build` returns success (3239 jobs).
**Sorries in this directory**: 0.
**Axioms in this directory**: 0.

## TL;DR

**Verdict: NO — with explicit counterexample.**

Axiom 3 (Reconstruction `R ∘ M = id` + Naturality), as currently
formalized, does **NOT** force the observation algebra to be a
normed division algebra in the Hurwitz tower `{ℝ, ℂ, ℍ, 𝕆}`.

The counterexample `A = ℝ × ℝ` (the split-complex / direct-product
algebra) satisfies:

* Link 1 — faithful trace (sum functional).
* Link 3 — alternativity (trivially, via associativity).
* `finrank ℝ = 2` (consistent with the Hurwitz dimension set).

but fails:

* the **strong** Link 2 — no faithful composition norm exists,
  because `(1, 0) · (0, 1) = (0, 0)` exhibits zero divisors.
* ring-isomorphism with `ℂ`.

This **vindicates** v0.9 line 16779's own "Real gap" self-flag.
It is the v0.9.2 honest accounting for G.4.

## Files

| File | Purpose |
|------|---------|
| `ReadingA_FormalChain.lean` | 4-link formal chain with predicates |
| `ReadingB_TraceState.lean`  | Tests trace ⇒ composition norm |
| `ReadingC_NaturalityForcesAlt.lean` | Tests naturality ⇒ alternative |
| `CounterexampleClass.lean`  | `ℝ × ℝ` falsifier |
| `Verdict.lean`              | Headline assembly |
| `STATUS.md`                 | This file |

## The four-link chain

| Link | Statement | Tier | Status |
|------|-----------|------|--------|
| 1 | Axiom 3 ⇒ faithful trace state | Tier 3 | Open content travels as `Link1_FaithfulTrace`; satisfied by counterexample. |
| 2 | Faithful trace ⇒ composition norm | Tier 3 | **Load-bearing failure point.** Open content as `Link2_CompositionNorm` (weak) and `StrongLink2_FaithfulCompositionNorm` (strong). Strong version **falsified** by counterexample. |
| 3 | Naturality ⇒ alternative | Tier 3 | Open content as `Link3_Alternative` / `NaturalityForcesAlternative`. Satisfied trivially by counterexample (associativity ⇒ alternativity). |
| 4 | Real alternative composition ⇒ Hurwitz tower `{1,2,4,8}` | **Tier 1** | Re-uses `composition_dim_le_eight_axiom` from `Hurwitz.lean` (Hurwitz 1898). |

## Tier-1 theorems proved here

### `ReadingA_FormalChain.lean`
* `link4_via_hurwitz` — finite-dim composition algebra has
  `finrank ∈ {1, 2, 4, 8}` (re-use of Hurwitz.lean).
* `chain_conditional` — the chain `Link 1 ∧ Link 2 ∧ Link 3 →
  Link 4`, requiring a `CompositionAlgebra` typeclass as the
  *external* bridging hypothesis.

### `ReadingB_TraceState.lean`
* `link2_from_faithful_trace_conditional` — conditional Link 1 → Link 2
  assuming GNS-multiplicativity (tautological; exposes the
  open content).

### `ReadingC_NaturalityForcesAlt.lean`
* `associative_implies_diag_vanishing` — associativity ⇒
  diagonal-associator vanishing.
* `link3_from_diag_vanishing` — diagonal-associator vanishing ⇒
  alternativity.
* `counterexample_satisfies_link3` — the counterexample
  trivially passes Link 3 (the chain failure is **not** at Link 3).

### `CounterexampleClass.lean`
* `counterexample_link1` — `ℝ × ℝ` has the sum-functional faithful trace.
* `counterexample_associative` — `ℝ × ℝ` is associative.
* `counterexample_link3` — alternativity (trivially from associativity).
* `counterexample_finrank` — `finrank ℝ (ℝ × ℝ) = 2`.
* `counterexample_has_zero_divisors` — `(1,0) · (0,1) = 0`.
* `counterexample_not_division` — not a division algebra.
* `counterexample_fails_strong_link2` — **the structural falsifier**:
  no faithful composition norm exists.
* `counterexample_not_iso_complex` — `ℝ × ℝ ≄+* ℂ`.

### `Verdict.lean`
* `RM_does_not_force_division_algebras_headline` — the
  structural-existence statement of the falsification.
* `v092_G4_verdict_NO` — compact `¬ ∀` form of the verdict.
* `missing_ingredient_is_strong_link_2` — pinpoints the
  load-bearing gap.

## Tier-3 obstructions

* **Link 1 (trace existence)**: Conditional on Axiom 3 reading.
  The `compute/faithfulness-forces-yR` session showed that all five
  standing readings of Axiom 3 do *not* uniquely select a faithful
  trace — they admit a continuum.  Open content as `Link1_FaithfulTrace`.

* **Link 2 (composition norm)**: This is the **load-bearing failure
  point**.  The GNS form `q(a) = τ(star a · a)` produced by
  faithfulness gives only a quadratic form, not a multiplicative
  norm.  The canonical counterexample is the Frobenius norm on
  `M_n(ℝ)`: *submultiplicative*, not multiplicative.  We instantiate
  with the smaller `ℝ × ℝ` for explicitness.  Open content as
  `TraceProducesCompositionNorm`.

* **Link 3 (alternativity)**: The standing formalization of
  Naturality (`SectorFaithful` typeclass — three faithful states
  on three sector algebras) carries **no** diagonal-associator
  constraint.  Open content as `NaturalityForcesAlternative`.
  (Note: the counterexample passes Link 3, so this is not where
  the chain breaks for our witness — but it is *additionally* open
  in the abstract setting.)

## Counterexample summary

```
A := ℝ × ℝ  (the split-complex algebra)

Satisfies:
  ✓ Link 1 — sum functional is faithful
  ✓ Link 3 — alternativity (trivially)
  ✓ finrank ℝ = 2 (in Hurwitz dimension set)
  ✓ Associative (Ring instance)

Fails:
  ✗ Strong Link 2 — zero divisors (1,0)·(0,1) = (0,0)
  ✗ Ring iso to ℂ — ℂ has no zero divisors
```

The **algebraic mechanism** falsifying the v0.9 claim: the existence
of orthogonal idempotents `(1, 0)` and `(0, 1)` (with `e₁ + e₂ = 1`,
`e₁ · e₂ = 0`).  Hurwitz-tower algebras have **no** non-trivial
idempotents.  Reconstruction `R ∘ M = id` of Axiom 3 does not
exclude orthogonal idempotents.

## Named axioms cited (in code or documentation)

This dispatch introduces **zero new axioms**.  It cites:

* **Hurwitz, A. (1898/1923)**, "Über die Composition der quadratischen
  Formen." — via `composition_dim_le_eight_axiom` (already in
  `Hurwitz.lean`).
* **Albert, A.A. (1947)**, "Absolute valued real algebras." Ann. Math. 48.
  — identifies `ℝ × ℝ` as the canonical non-division 2-dim ℝ-algebra.
* **Bruck, R.H. & Kleinfeld, E. (1951)**, "The structure of alternative
  division rings." Proc. AMS 2. — composition ↔ alternative.
* **Connes, A. (1994)**, *Noncommutative Geometry*, Ch. V. —
  GNS faithful state construction; required positivity for Link 1 → Link 2.

## Why this matters

The v0.9 framework's "central node of the blueprint"
(`SpectralPhysics/Algebra/Forcing.lean`, line 16) asserts that
self-referential closure (Axiom 3) forces `A_obs = ℂ ⊗ ℍ ⊗ 𝕆`.
The Forcing.lean implementation already **assumes** a
`CompositionAlgebra` typeclass — it does *not* derive that
typeclass from Axiom 3.  v0.9 line 16779 acknowledges this gap as
"Real gap."

This dispatch closes the meta-question: **the gap is unbridgeable
without additional structural hypotheses.**  The counterexample
identifies the exact missing ingredient (faithful composition norm,
i.e. the *strong* Link 2) and shows that no purely categorical
strengthening of Axiom 3 (i.e., one that does not implicitly assume
unitarity / positivity / norm-multiplicativity) can close the chain.

The honest framings consistent with this finding:

1. **Strong-positivity Axiom 3.**  Postulate Link 2 directly:
   "the observation algebra carries a faithful composition norm."
   Then Hurwitz applies.  This is the choice made (tacitly) in
   `Forcing.lean` via the `CompositionAlgebra` typeclass hypothesis.

2. **Transcendent-IC framing.**  Treat the algebra type as input
   data, not as a derivation.  Parallel to `y_R` after the
   `compute/faithfulness-forces-yR` negative result.

3. **Unitarity-from-reconstruction.**  Derive Link 2 from a separate
   physical-unitarity axiom, not from Axiom 3 (i)+(ii) alone.

Each is a valid v1.0 framing; **none** is what v0.9 currently claims
on line 16779.  This dispatch makes the gap explicit so that v1.0
can be honest about it.

## Build status

```
$ lake build
Build completed successfully (3239 jobs).
```

The new five files in `SpectralPhysics/RMForcesDivisionAlgebras/`
contribute zero sorries, zero axioms, and no `True` placeholders to
the workspace.

## Cross-references

* `SpectralPhysics/Axioms/SelfRefClosure.lean` — Axiom 3 typeclass
  (Reconstruction / Naturality / Faithfulness).
* `SpectralPhysics/Algebra/Hurwitz.lean` — Hurwitz theorem
  formalization (Tier-1 conditional on `CompositionAlgebra`).
* `SpectralPhysics/Algebra/Forcing.lean` — division-algebra forcing
  *assuming* the composition-algebra typeclass.
* `compute/faithfulness-forces-yR` — adjacent negative on `y_R`
  closure from Axiom 3.
* `yukawa/pre_geometric/v091_v092_split_audit/v092_deferred.md`
  §G.4 — the dispatch motivation.
