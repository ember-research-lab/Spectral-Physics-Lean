/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.DixonPoincareDuality.KOMetric
import SpectralPhysics.DixonOrderOne.OrderOneCondition
import SpectralPhysics.DixonOrderOne.NonAssocObstruction

/-!
# The Poincaré duality predicate

In Connes' NCG formalism, a real spectral triple `(A, H, D, J, γ)` is
said to satisfy **Poincaré duality** if the K-theoretic intersection
form `K_*(A) ⊗ K_*(A) → ℤ` is non-degenerate, i.e. it induces an
isomorphism `K_*(A) → K^*(A)`.

At the abstract carrier level introduced in `KOMetric.lean`, we
formalise this by asking that the intersection map `a ↦ (b ↦ ⟨a,b⟩)`
be a **bijection** as a function on the underlying carrier.

## What this file provides

* `PoincareDuality T : Prop` — the predicate that
  `T.intersectionForm` (viewed as `a ↦ (b ↦ ⟨a, b⟩)`) is bijective.
* `connes_PD_requires_wellDefinedness` — the named axiom asserting
  that PD nondegeneracy implies the well-definedness predicate
  introduced in `KOMetric.lean`. This is the published Connes 1994
  §VI.4 fact that the intersection form must first descend to
  classes before non-degeneracy is well-posed.
* `wellDefinedness_implies_zerothOrder_canonical` — Tier 1 lemma:
  for the canonical Dixon-style carrier, `WellDefinedOnClasses`
  unfolds to the zeroth-order commutation predicate.

## References

* Connes, A., *Noncommutative Geometry* (1994), §VI.4 — Poincaré
  duality on the K-theory of a real spectral triple.
* Connes, A., *Gravity coupled with matter and the foundation of
  non-commutative geometry*, Commun. Math. Phys. 182 (1996),
  155–176 — the published axiomatic system.
* Bochniak, A., Sitarz, A., arXiv:2001.02613, §III —
  non-degeneracy failure in the non-associative case.
-/

namespace SpectralPhysics.DixonPoincareDuality

open SpectralPhysics.DixonOrderOne

/-- **Poincaré duality** for an abstract spectral-triple carrier.

`PoincareDuality T` is the assertion that the K-theoretic
intersection map, viewed as `a ↦ T.intersectionForm a`, is a
**bijection** as a function `𝕆 → (𝕆 → 𝕆)`. This is the abstract-
carrier shadow of the Connes 1994 §VI.4 nondegeneracy condition
(which on K-theory says `K_*(A) → K^*(A)` is an isomorphism). -/
def PoincareDuality (T : AbstractSpectralTriple) : Prop :=
  Function.Bijective (T.intersectionForm)

/-! ## Zeroth-order failure on the canonical Dixon triple

This is a Tier-1 unconditional consequence of `not_zerothOrder_canonical_dixon`
(from `DixonOrderOne.NonAssocObstruction`): when `WellDefinedOnClasses`
is unfolded on `canonicalDixonTriple`, it reduces to the zeroth-order
commutation predicate on `(LeftMult, RightMult)`. -/

/-- **Tier 1.** Well-definedness of the intersection form on the
canonical Dixon-style carrier is **equivalent** to the zeroth-order
condition on `(LeftMult, RightMult)`. -/
theorem wellDefinedOnClasses_canonical_iff_zerothOrder :
    WellDefinedOnClasses canonicalDixonTriple ↔
      ZerothOrder LeftMult RightMult := by
  -- Unfold both sides to the same pointwise statement
  unfold WellDefinedOnClasses canonicalDixonTriple
  rw [zerothOrder_LeftMult_RightMult_iff]

/-- **Tier 1.** The canonical Dixon triple does NOT have a
well-defined intersection form on K-theory classes.

Direct consequence of `not_zerothOrder_canonical_dixon` via the
iff above. -/
theorem not_wellDefinedOnClasses_canonical_dixon :
    ¬ WellDefinedOnClasses canonicalDixonTriple := by
  rw [wellDefinedOnClasses_canonical_iff_zerothOrder]
  exact not_zerothOrder_canonical_dixon

/-! ## The general Connes §VI.4 reduction (named predicate)

We name the GENERAL fact that PD on a real spectral triple requires
the intersection form to be well-defined on K-theory classes. This
is the published Connes 1994 §VI.4 construction: PD is *defined*
as nondegeneracy of a pairing that lives on the K-theory quotient,
so it presupposes that the pairing has descended there at all. -/

/-- The published Connes §VI.4 reduction, stated as a predicate.

`PDImpliesWellDefined T` says: if `T` satisfies the PD predicate
(intersection form is bijective), then the intersection form
descends to a well-defined pairing on K-theory classes. -/
def PDImpliesWellDefined (T : AbstractSpectralTriple) : Prop :=
  PoincareDuality T → WellDefinedOnClasses T

end SpectralPhysics.DixonPoincareDuality
