# DixonPoincareDuality — non-associativity obstruction to Poincaré duality

**Date:** 2026-05-11
**Branch:** `compute/dixon-poincare-duality`
**Target:** v0.9.2 deferred item B.2
       (v0.9 line 6736; sister item to B.1 / `compute/dixon-order-one`)
**Build:** `lake build SpectralPhysics` succeeds (3241 jobs).

## Verdict — **NO** (honest negative)

Under the standard NCG real-spectral-triple formalism (Connes 1994
§VI.4), **the canonical Dixon-algebra spectral triple does NOT admit
Poincaré duality.** The obstruction is the same non-associativity of
the octonion factor `𝕆 = CD(ℍ)` that breaks the order-one axiom in
B.1: left- and right-multiplication on `𝕆` fail to commute, so the
K-theoretic intersection form
`⟨[a], [b]⟩ := index(γ ∘ D ∘ π(a) ∘ J ∘ π(b)* ∘ J⁻¹)`
cannot descend to a well-defined pairing on K-theory classes — let
alone be non-degenerate.

The Lean theorem
`dixon_pd_obstruction :
 ¬ ∃ T, IsCanonicalDixon T ∧ PoincareDuality T`
records this. The specialisation
`dixon_pd_fails_canonical : ¬ PoincareDuality canonicalDixonTriple`
gives the headline on the concrete carrier.

This matches the obstruction analysis of Bochniak–Sitarz
(arXiv:2001.02613 §III) and Boyle–Farnsworth (arXiv:1910.11888).

## Relationship to B.1 (`compute/dixon-order-one`)

This branch **re-uses** the algebraic-level witnesses from B.1:

| Re-used from B.1                          | Used as                                                              |
| ----------------------------------------- | -------------------------------------------------------------------- |
| `quaternion_not_commutative`              | algebraic seed for the obstruction                                   |
| `octonion_factor_not_associative`         | Cayley-Dickson lift of the seed                                      |
| `associator_nonzero_witness`              | algebraic obstruction witness                                        |
| `LR_commutator_nonzero_witness`           | operator-level obstruction witness                                   |
| `ZerothOrder`                             | predicate definition                                                 |
| `zerothOrder_LeftMult_RightMult_iff`      | structural bridge                                                    |
| `not_zerothOrder_canonical_dixon`         | unconditional Tier-1 negative result (consumed without re-derivation) |

Three files from B.1 are present in this worktree as **read-only
dependencies**:
* `SpectralPhysics/DixonOrderOne/DixonAlgebra.lean`
* `SpectralPhysics/DixonOrderOne/OrderOneCondition.lean`
* `SpectralPhysics/DixonOrderOne/NonAssocObstruction.lean`

**They are NOT committed on this branch.** When B.1 merges to
`v0.9.2-merge-staging`, this branch will pick them up; the
worktree-local copies here are bit-identical to the B.1 source.

## Files (this branch's authored content)

| File                            | Status                                          |
| ------------------------------- | ----------------------------------------------- |
| `KOMetric.lean`                 | 0 `sorry`, **0 axioms**, abstract triple + intersection form |
| `PoincareDualityAxiom.lean`     | 0 `sorry`, **0 axioms**, 2 Tier-1 theorems      |
| `NonAssocObstructsPD.lean`      | 0 `sorry`, **0 axioms**, 3 Tier-1 theorems (conditional on named-axiom hypotheses) |
| `Verdict.lean`                  | 0 `sorry`, **2 named axioms** + 4 headline theorems |
| `STATUS.md`                     | this file                                       |

## What got proved (Tier 1, no axioms beyond Lean kernel)

### Structural-level

* `wellDefinedOnClasses_canonical_iff_zerothOrder`:
  `WellDefinedOnClasses canonicalDixonTriple ↔ ZerothOrder LeftMult RightMult`
  — the structural bridge: the descent-to-classes predicate on the
  canonical carrier *is* the zeroth-order commutation.

* `not_wellDefinedOnClasses_canonical_dixon`:
  `¬ WellDefinedOnClasses canonicalDixonTriple`
  — direct consequence of B.1's `not_zerothOrder_canonical_dixon`
  via the iff above; depends on zero non-kernel axioms.

### Conditional-on-named-axiom level

* `PD_implies_zerothOrder_canonical`:
  given a hypothesis `PDImpliesWellDefined canonicalDixonTriple`,
  `PoincareDuality canonicalDixonTriple → ZerothOrder LeftMult RightMult`.

* `PD_fails_for_canonical_dixon`:
  given the same hypothesis,
  `¬ PoincareDuality canonicalDixonTriple`.

* `PD_fails_for_dixon`:
  given the *uniform* hypothesis applying to every Dixon-canonical
  carrier, `¬ ∃ T, IsCanonicalDixon T ∧ PoincareDuality T`.

The conditional hypotheses are the standard Connes §VI.4 reduction;
they are introduced as predicates first and named as axioms only in
`Verdict.lean`.

## Named axioms (2 total, with full citations)

### `Verdict.lean` (2)

| Axiom                                     | Role                                                                                                                          | Citation                                                                                                                                                |
| ----------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `connes_PD_definition`                    | "PD ⇒ intersection form descends to classes" for *every* abstract spectral triple — the published §VI.4 definition step | Connes, A., *Noncommutative Geometry* (1994), §VI.4                                                                                                     |
| `bochniak_sitarz_PD_obstruction`          | The same reduction applied uniformly to *Dixon-canonical* carriers; cited explicitly in the non-associative literature   | Bochniak, A., Sitarz, A., *Spectral interaction between universes*, arXiv:2001.02613, §III; Connes, A., *Noncommutative Geometry* (1994), §VI.4 |

Both axioms encode **general facts** of the published NCG and
non-associative-NCG literature: PD on a real spectral triple is
*defined* (Connes §VI.4) as non-degeneracy of an intersection form
on K-theory; this presupposes the form descends to K-theory classes,
which in turn requires the zeroth-order commutation of the
representation and its opposite. We do NOT formalise the full real-
spectral-triple axiomatics (KO-dimension, J-structure, ε signs,
regularity); we name the implication.

### Smuggling check

The axioms are the *forward* shadow of the published reduction; they
are **not** assertions of the Dixon-specific obstruction. Specifically:

* They do NOT say "the Dixon PD fails." They say "in general, PD
  presupposes the K-theoretic pairing's well-definedness on classes
  (which requires zeroth-order)."
* The Dixon-specific obstruction
  (`not_wellDefinedOnClasses_canonical_dixon`) is **unconditional
  Tier 1** — it depends on no axioms beyond Lean's kernel.
* The headline theorem `dixon_pd_obstruction` chains the
  unconditional negative result with the named-axiom reduction to
  produce the verdict. Remove the named axioms: the unconditional
  zeroth-order failure (and hence the unconditional well-definedness
  failure) still stands; only the chain to "no Dixon-canonical `T`
  satisfies PD" relies on the named reductions.
* `bochniak_sitarz_PD_obstruction` is logically a consequence of
  `connes_PD_definition` (it is the specialisation to
  Dixon-canonical carriers). We name it separately to honour the
  citation discipline — the published non-associative analysis is
  in Bochniak–Sitarz, not Connes 1994 directly.

## Predicates carrying open content

| Predicate                                                    | Module                              | What it carries                                                                                                                                |
| ------------------------------------------------------------ | ----------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------- |
| `WellDefinedOnClasses T`                                     | `KOMetric.lean`                     | "The intersection form descends to a well-defined pairing on K-theory classes." NOT trivially true — on the canonical Dixon triple it FAILS. |
| `PoincareDuality T`                                          | `PoincareDualityAxiom.lean`         | "The intersection form is a bijection." Predicate definition.                                                                                  |
| `PDImpliesWellDefined T`                                     | `PoincareDualityAxiom.lean`         | The published §VI.4 reduction, stated as a `Prop` so that any consumer must explicitly invoke it.                                              |
| `IsCanonicalDixon T`                                         | `NonAssocObstructsPD.lean`          | "`T` uses the canonical `(LeftMult, RightMult)` action data."                                                                                  |

## Sorries

**0 sorries.** Verified by
`grep -rn 'sorry\|admit' SpectralPhysics/DixonPoincareDuality/`
(only docstring substring matches; no actual tactic uses).

## True placeholders

**0 True placeholders.**

## Definitional triviality check

Anti-pattern check (rule 3 of the audit discipline):

* `PoincareDuality T` is NOT trivially `True`. It is
  `Function.Bijective (T.intersectionForm)` — a genuine predicate on
  the carrier.
* `WellDefinedOnClasses T` is NOT trivially `True`. After unfolding
  on `canonicalDixonTriple` it becomes the zeroth-order commutation
  predicate `∀ a b x, LeftMult a (RightMult b x) = RightMult b (LeftMult a x)`,
  which by B.1's `not_zerothOrder_canonical_dixon` provably fails.
* `IsCanonicalDixon T` is a pointwise equality predicate, not a
  numerical anchor.

## `#print axioms` audit

```
'SpectralPhysics.DixonPoincareDuality.dixon_pd_obstruction'
  depends on axioms: [propext, Classical.choice, Quot.sound,
                      bochniak_sitarz_PD_obstruction]

'SpectralPhysics.DixonPoincareDuality.dixon_pd_fails_canonical'
  depends on axioms: [propext, Classical.choice, Quot.sound,
                      connes_PD_definition]

'SpectralPhysics.DixonPoincareDuality.dixon_pd_has_nonzero_associator'
  depends on axioms: [propext, Classical.choice, Quot.sound]

'SpectralPhysics.DixonPoincareDuality.dixon_pd_not_wellDefined'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

The chain from B.1's `quaternion_not_commutative` (via
Cayley-Dickson) to `dixon_pd_not_wellDefined` and
`dixon_pd_has_nonzero_associator` is purely Tier 1. The two named
axioms enter only at `dixon_pd_obstruction` and
`dixon_pd_fails_canonical`, and are the published Connes / Bochniak–
Sitarz reductions.

## Why this is honest

1. **No axiomatised numerical anchors.** No `def := 6`, no `8 = 8`
   by `rfl`, no engineered constants. The obstruction is structural.

2. **The named axioms are general.** Both
   `connes_PD_definition` and `bochniak_sitarz_PD_obstruction`
   assert properties of *any* (resp. *any Dixon-canonical*)
   abstract spectral-triple carrier, NOT Dixon-specific verdicts.
   They cite Connes 1994 §VI.4 and Bochniak–Sitarz 2021 §III
   that explicitly works through the non-associative case.

3. **The Dixon-specific obstruction is unconditional.**
   `not_wellDefinedOnClasses_canonical_dixon` depends on zero
   non-kernel axioms. The non-associativity of `𝕆` is proved from
   Mathlib's `Quaternion ℝ` and the Cayley-Dickson construction;
   the descent failure follows from the explicit `i, j ∈ ℍ`
   witness through B.1's machinery.

4. **The verdict is NEGATIVE.** We do not pretend to close the
   Dixon PD in any positive sense; we honestly conclude that under
   the canonical (LeftMult, RightMult) representation, no Dirac /
   J-structure choice can satisfy PD. This matches the framework's
   own diagnosis in v0.9 line 6736 and the Bochniak–Sitarz /
   Boyle–Farnsworth literature.

5. **No re-derivation of the B.1 obstruction.** We import and
   consume `not_zerothOrder_canonical_dixon` and
   `LR_commutator_nonzero_witness` from `DixonOrderOne`. The
   PD-specific content is the *bridge* from PD to the zeroth-order
   condition (via `WellDefinedOnClasses`), not a re-proof of the
   algebraic obstruction.

## What this does NOT close

* **A non-canonical representation might salvage PD.** As with B.1,
  some proposals (Boyle–Farnsworth 2019) use a Jordan-algebra
  reformulation in which the relevant action is not `(L, R)` but a
  Jordan-product action. Whether *that* representation admits a
  non-degenerate K-theoretic intersection form on the Dixon algebra
  is an open problem in NCG-EXT. This module does not address it;
  it pins down the *canonical* failure.

* **The full operator-theoretic K-theory of non-associative
  algebras** (e.g. Mygdalas / non-associative K-theory) is NOT
  formalised here. We do not commit to a specific Lean-level
  category of finitely-generated projective modules. The predicate
  `WellDefinedOnClasses` encodes the descent requirement at the
  level the obstruction is actually visible: bracketing-
  independence of the `π`/`π'` composition.

## Build status

```
$ lake build SpectralPhysics
✔ [3240/3241] Built SpectralPhysics (1.0s)
Build completed successfully (3241 jobs).
```

All four files build cleanly with 0 errors. The warnings shown are
inherited from unrelated modules (`Hurwitz.lean`,
`FaithfulnessForcesYR/`) and pre-exist on `main`.
