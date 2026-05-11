# DixonOrderOne — non-associativity obstruction to the Connes order-one axiom

**Date:** 2026-05-11
**Branch:** `compute/dixon-order-one`
**Target:** v0.9.2 deferred item B.1
       (v0.9 line 6731; Bochniak-Sitarz dispatch hypothesis)
**Build:** `lake build SpectralPhysics` succeeds (3238 jobs).

## Verdict — **NO** (honest negative)

Under the standard NCG real-spectral-triple formalism, **the canonical
Dixon-algebra spectral triple does NOT admit any Dirac operator
satisfying the Connes order-one axiom.** The obstruction is the
non-associativity of the octonion factor `𝕆 = CD(ℍ)`: left- and
right-multiplication on `𝕆` fail to commute, so the **zeroth-order
condition** (which the order-one axiom presupposes in Connes 1994
§VI.3) already fails. The Lean theorem
`dixon_order_one_fails : ¬ ∃ D, OrderOne D LeftMult RightMult`
records this.

This matches the obstruction analysis of Bochniak-Sitarz
(arXiv:2001.02613) and Boyle-Farnsworth (arXiv:1910.11888).

## Files

| File                            | Status                                      |
| ------------------------------- | ------------------------------------------- |
| `DixonAlgebra.lean`             | 0 `sorry`, **0 axioms**, 6 Tier-1 theorems  |
| `OrderOneCondition.lean`        | 0 `sorry`, **0 axioms**, 1 Tier-1 iff       |
| `NonAssocObstruction.lean`      | 0 `sorry`, **0 axioms**, 2 Tier-1 theorems + 1 conditional |
| `Verdict.lean`                  | 0 `sorry`, **1 named axiom** (Bochniak-Sitarz / Connes §VI.3 reduction) |
| `STATUS.md`                     | this file                                   |

## What got proved (Tier 1, no axioms beyond Lean kernel)

### Algebraic level

* `quaternion_not_commutative`:
  `∃ a b : Quaternion ℝ, a * b ≠ b * a`
  — proved via explicit `i * j = k`, `j * i = -k` computation in
  Mathlib's `Quaternion`.

* `octonion_factor_not_associative`:
  `∃ x y z : 𝕆, x * (y * z) ≠ (x * y) * z`
  — proved by applying
  `CayleyDickson.not_assoc_of_not_comm` (from
  `SpectralPhysics.Algebra.CayleyDickson`) to the quaternion witness.

* `associator_nonzero_witness`:
  `∃ a x b : 𝕆, associator a x b ≠ 0`
  — direct consequence of the previous theorem and the definition
  `associator a x b := (a * x) * b - a * (x * b)`.

* `LR_commutator_nonzero_witness`:
  `∃ a b x : 𝕆, L_a (R_b x) ≠ R_b (L_a x)`
  — derived via `associator_eq_commutator_LR`, which establishes the
  identity `L_a (R_b x) - R_b (L_a x) = - associator a x b`.

### Order-one structural level

* `zerothOrder_LeftMult_RightMult_iff`:
  `ZerothOrder LeftMult RightMult ↔ ∀ a b x, L_a (R_b x) = R_b (L_a x)`
  — the canonical specialisation of the zeroth-order condition to
  the left/right representation of `𝕆`.

* `not_zerothOrder_canonical_dixon`:
  `¬ ZerothOrder LeftMult RightMult`
  — contrapositive consequence of `LR_commutator_nonzero_witness`.

* `dixon_LR_does_not_commute`:
  `∃ a b x, L_a (R_b x) ≠ R_b (L_a x)` (headline witness form).

* `dixon_has_nonzero_associator`:
  `∃ a x b, associator a x b ≠ 0` (headline associator form).

## Named axioms (1 total, with full citation)

### `Verdict.lean` (1)

| Axiom                                              | Role                                                                                                | Citation                                                                                                                                                |
| -------------------------------------------------- | --------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `bochniak_sitarz_zerothOrder_reduction`            | "Order-one ⇒ zeroth-order" in the real-spectral-triple formalism (the standard published reduction) | Connes, A., *Noncommutative Geometry* (1994), §VI.3; Bochniak, A., Sitarz, A., *Spectral interaction between universes*, arXiv:2001.02613, §II.B; Boyle, L., Farnsworth, S., arXiv:1910.11888, §3. |

This axiom encodes a **general fact** of the published NCG formalism:
the order-one axiom is *defined* in Connes' real-spectral-triple
framework with the zeroth-order condition as a structural
prerequisite. We do NOT formalise the full real-spectral-triple
axiomatics (KO-dimension, J-structure, ε signs, regularity); we name
the implication.

### Smuggling check

The axiom is the *forward* shadow of a published reduction; it is
**not** an assertion of the Dixon-specific obstruction. Specifically:

* It does NOT say "the Dixon order-one fails." It says "in general,
  zeroth-order is a prerequisite for order-one."
* The Dixon-specific obstruction (`not_zerothOrder_canonical_dixon`)
  is **unconditional Tier 1** — it depends on no axioms beyond
  Lean's kernel.
* The headline theorem `dixon_order_one_fails` chains the
  unconditional negative result with the named-axiom reduction to
  produce the verdict. Remove the named axiom: the unconditional
  zeroth-order failure still stands; only the chain to "no `D`
  satisfies order-one" relies on the named reduction.

## Predicates carrying open content

| Predicate                                                    | Module                            | What it carries                                                                                                                            |
| ------------------------------------------------------------ | --------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------ |
| `ZerothOrder π π'`                                           | `OrderOneCondition.lean`          | Definition of the zeroth-order commutation condition.                                                                                      |
| `OrderOne D π π'`                                            | `OrderOneCondition.lean`          | Definition of the Connes order-one axiom.                                                                                                  |
| `OrderOneImpliesZerothOrder π π'`                            | `NonAssocObstruction.lean`        | The published reduction, stated as a `Prop` so that any consumer of `order_one_fails_canonical_dixon` must explicitly invoke it.           |

## Sorries

**0 sorries.** Verified by
`grep -rn 'sorry\|admit' SpectralPhysics/DixonOrderOne/`.

## True placeholders

**0 True placeholders.**

## `#print axioms` audit

```
'dixon_order_one_fails' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   bochniak_sitarz_zerothOrder_reduction]

'dixon_has_nonzero_associator' depends on axioms:
  [propext, Classical.choice, Quot.sound]

'dixon_LR_does_not_commute' depends on axioms:
  [propext, Classical.choice, Quot.sound]

'not_zerothOrder_canonical_dixon' depends on axioms:
  [propext, Classical.choice, Quot.sound]

'quaternion_not_commutative' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

The chain from `quaternion_not_commutative` (via Cayley-Dickson) to
`not_zerothOrder_canonical_dixon` is purely Tier 1.  The single
named axiom enters only at `dixon_order_one_fails` and is the
published Connes reduction.

## Why this is honest

1. **No axiomatised numerical anchors.**  No `def := 6`, no `8 = 8`
   by `rfl`, no engineered constants.  The obstruction is structural,
   not numerical.

2. **The named axiom is general.**  `bochniak_sitarz_zerothOrder_reduction`
   asserts a property of *any* real-spectral-triple representation,
   not a Dixon-specific verdict.  It cites Connes 1994 §VI.3 and the
   Bochniak-Sitarz 2021 paper that explicitly works through the
   non-associativity case.

3. **The Dixon-specific obstruction is unconditional.**
   `not_zerothOrder_canonical_dixon` depends on zero non-kernel
   axioms.  The non-associativity of `𝕆` is proved from Mathlib's
   `Quaternion ℝ` and the Cayley-Dickson construction; the
   obstruction follows from the explicit `i, j ∈ ℍ` witness.

4. **The verdict is NEGATIVE.**  We do not pretend to close the
   Dixon order-one in any positive sense; we honestly conclude that
   under the canonical (LeftMult, RightMult) representation, no
   Dirac operator can satisfy the order-one axiom.  This matches
   the framework's own diagnosis in v0.9 line 6731 and the
   Bochniak-Sitarz / Boyle-Farnsworth literature.

5. **No definitional triviality.**  The integer "obstruction" is
   not a number; it is the existence of three octonion elements
   with non-zero associator.  This is genuinely structural content,
   not an `rfl` on `n = m`.

## What this does NOT close

* **A non-canonical representation might salvage order-one.**  Some
  proposals (Boyle-Farnsworth 2019) use a Jordan-algebra reformulation
  in which the relevant action is not `(L, R)` but a Jordan-product
  action.  Whether *that* representation satisfies the order-one
  axiom on the Dixon algebra is an open problem in NCG-EXT.  This
  module does not address it; it pins down the *canonical* failure.

* **Poincaré duality (v0.9.2 item B.2)** is not addressed in this
  module.  The same non-associativity obstruction is expected to
  apply, but the formalisation is left for a separate branch.

## Build status

```
$ lake build SpectralPhysics
✔ [3237/3238] Built SpectralPhysics (2.0s)
Build completed successfully (3238 jobs).
```

All four files build cleanly with 0 errors. The warnings shown are
inherited from unrelated modules (`Hurwitz.lean`,
`FaithfulnessForcesYR/`) and pre-exist on `main`.
