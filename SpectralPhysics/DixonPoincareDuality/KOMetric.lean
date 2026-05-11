/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.DixonOrderOne.DixonAlgebra

/-!
# K-theoretic intersection form (KO-metric) for a real spectral triple

In Connes' NCG formalism (Connes 1994 §VI.4), a real spectral triple
`(A, H, D, J, γ)` of KO-dimension `n` carries an intersection form
on K-theory
```
⟨[e], [f]⟩ := index(γ ∘ D ∘ e ∘ J ∘ f ∘ J⁻¹)
```
For Poincaré duality the resulting pairing
`K_*(A) ⊗ K_*(A) → ℤ` is required to be **non-degenerate**, i.e. it
induces an isomorphism `K_*(A) → K^*(A)`.

This file defines an *abstract* spectral-triple record sufficient to
state Poincaré duality at the level of a `Prop`, **without**
committing to a full operator-theoretic formalisation (which would
duplicate vast machinery beyond what is needed for the v0.9.2 B.2
verdict).

The carrier we use is the Dixon-octonion factor `𝕆 = CD(ℍ)` from
`DixonOrderOne.DixonAlgebra`; the algebra is `OctonionFactor`. The
*opposite action* — needed to even *state* the intersection form —
is the right-multiplication map `RightMult`, already defined in
`DixonOrderOne.DixonAlgebra`. The same non-associativity that blocks
the order-one axiom (B.1) blocks the well-definedness of the
opposite action's commutation with left multiplication — which is
the kernel-pinning condition that the intersection form requires to
be a *well-defined* pairing on classes.

## What this file provides

* `AbstractSpectralTriple`: a Lean structure carrying just the data
  needed to state Poincaré duality at the predicate level — the
  representation `π`, the opposite `π'`, and a candidate "K-theoretic
  intersection map" `intersectionMap` of type `𝕆 → 𝕆`.
* `intersectionForm`: the value `(intersectionMap a) b` viewed as the
  pairing of classes.
* `wellDefinedOnClasses`: the predicate that the intersection map
  factors through the commutation `[π(a), π'(b)] = 0` so that it
  descends to K-theory classes.

The crucial observation: `wellDefinedOnClasses` *implies* the
zeroth-order condition `ZerothOrder π π'`, because the intersection
form, by Connes 1994 §VI.4, is constructed by composing the
representation and the opposite — and the composition is only a
well-defined map on `K_0 ⊗ K_0` once the two actions commute.

We carry this implication as a NAMED PREDICATE-LEVEL HYPOTHESIS
(see `PoincareDualityAxiom.lean`); the predicate itself lives here.

## References

* Connes, A., *Noncommutative Geometry* (1994), §VI.4 (intersection
  form on K-theory; non-degeneracy as Poincaré duality).
* Connes, A., *Gravity coupled with matter and the foundation of
  non-commutative geometry*, Commun. Math. Phys. 182 (1996),
  155–176 — the K-theoretic intersection form.
* Bochniak, A., Sitarz, A., arXiv:2001.02613 §III — non-degeneracy
  failure for Dixon-type triples.
-/

namespace SpectralPhysics.DixonPoincareDuality

open SpectralPhysics.DixonOrderOne

/-- A minimal abstract real spectral triple carrier sufficient to
state Poincaré duality at the predicate level.

The data:
* `π`: representation of the algebra as endomorphisms.
* `π'`: opposite representation (acts on the right, via `J`).
* `intersectionMap`: a map encoding the K-theoretic pairing — for a
  fixed `[e]`, `intersectionMap a` returns the index-class
  representative `γ ∘ D ∘ π(a) ∘ J ∘ π(·)* ∘ J⁻¹` viewed as a map
  on the carrier.

We do NOT axiomatise the Dirac operator or J-structure here; they
are absorbed into `intersectionMap`. The PD predicate is stated
purely on `intersectionMap`. -/
structure AbstractSpectralTriple where
  /-- The representation of the algebra `𝕆` on itself. -/
  π : OctonionFactor → (OctonionFactor → OctonionFactor)
  /-- The opposite representation (right action through J). -/
  π' : OctonionFactor → (OctonionFactor → OctonionFactor)
  /-- The K-theoretic intersection map.

  Heuristically, `intersectionMap a` is the operator
  `γ ∘ D ∘ π(a) ∘ J ∘ (·)* ∘ J⁻¹` whose index (on the relevant
  Hilbert space sector) gives `⟨[a], [b]⟩`. We package it as an
  endomorphism of `OctonionFactor` to keep the data minimal. -/
  intersectionMap : OctonionFactor → (OctonionFactor → OctonionFactor)

/-- The intersection-form pairing of two classes.

For `T : AbstractSpectralTriple` and elements `a, b : 𝕆`, the value
`T.intersectionForm a b := T.intersectionMap a b` is the pairing
`⟨[a], [b]⟩` of K-theory classes. -/
def AbstractSpectralTriple.intersectionForm
    (T : AbstractSpectralTriple) (a b : OctonionFactor) : OctonionFactor :=
  T.intersectionMap a b

/-! ## Well-definedness on classes

For the intersection form `⟨·, ·⟩` to descend to a pairing on
K-theory classes, the construction must respect the equivalence on
finitely-generated projective modules. In Connes 1994 §VI.4, this
descent requires the zeroth-order commutation
`[π(a), π'(b)] = 0`: the representation and the opposite must
commute pointwise, so that the composition
`π(a) ∘ J ∘ π(b)* ∘ J⁻¹` is well-defined as an operator on the
*combined* `A ⊗ A^op`-module structure of the Hilbert space.

When the algebra is non-associative — as for `𝕆` — the opposite
representation `π' = RightMult` fails to commute with the
representation `π = LeftMult`, so the intersection form's domain
of definition collapses (it depends on the choice of bracketing,
which is precisely what the associator measures). -/

/-- `WellDefinedOnClasses T` says: the intersection form induced by
`T` descends to a well-defined pairing on K-theory classes.

Operationally we encode the descent condition as **independence of
the bracketing of the `π`/`π'` composition**: for every
`a, b, x : 𝕆`,
```
(π(a) ∘ π'(b)) x = (π'(b) ∘ π(a)) x.
```
This is exactly the zeroth-order commutation of the representation
and the opposite — which, by Connes 1994 §VI.4, is *precisely*
the descent condition for the intersection form to land on the
quotient `K_0(A) ⊗ K_0(A)`.

The predicate is NOT trivially true: on the Dixon octonion factor
it FAILS at the explicit `i, j` witness inherited via Cayley-Dickson
from `Quaternion ℝ`. -/
def WellDefinedOnClasses (T : AbstractSpectralTriple) : Prop :=
  ∀ a b x : OctonionFactor,
    (T.π a) (T.π' b x) = (T.π' b) (T.π a x)

/-- The canonical Dixon-style spectral-triple carrier:
`(π, π') = (LeftMult, RightMult)`, with `intersectionMap a b` taken
to be the standard composition
`(LeftMult a) ∘ (RightMult b)` (the *naive* K-theoretic pairing).

This is the canonical "left-acts-by-multiplication, opposite-acts-
by-right-multiplication" choice that the Dixon-type construction
forces. -/
def canonicalDixonTriple : AbstractSpectralTriple where
  π := LeftMult
  π' := RightMult
  intersectionMap := fun a => fun x => LeftMult a (RightMult a x)
  -- The intersectionMap value is irrelevant for the obstruction;
  -- what matters is that any choice of intersectionMap defined via
  -- composition of `π` and `π'` inherits their non-commutation.

end SpectralPhysics.DixonPoincareDuality
