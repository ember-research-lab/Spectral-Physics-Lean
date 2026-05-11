/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.DixonOrderOne.DixonAlgebra

/-!
# Connes' order-one axiom (operator-level formulation)

The Connes order-one condition for a spectral triple `(A, H, D, J)` is
```
∀ a b ∈ A,   [ [D, π(a)], J π(b)* J⁻¹ ] = 0
```
where `π : A → B(H)` is the representation and `b ↦ J π(b)* J⁻¹` is
the opposite (commutant) action.  The condition is part of a
two-condition stack:

* **Zeroth-order condition** (Connes 1994 §VI.3): the two actions
  commute,
  `∀ a b ∈ A, [π(a), J π(b)* J⁻¹] = 0`.
* **First-order condition** (Connes 1994 §VI.4 / "order-one axiom"):
  `[D, π(a)]` commutes with `J π(b)* J⁻¹` for every `a, b`.

The standard development *assumes* the zeroth-order condition holds,
then asks the first-order condition.  Equivalently, the
zeroth-order condition is necessary for the first-order axiom to be
well-posed in the published Connes formalism.

We formalise this at the **operator level** on a generic carrier type
`H = OctonionFactor`.  Predicates:
```
ZerothOrder π π' :=
  ∀ a b, commutator (π a) (π' b) = 0
OrderOne D π π' :=
  ∀ a b, commutator (commutator D (π a)) (π' b) = 0
```
For the canonical Dixon-style representation `π = LeftMult`,
`π' = RightMult`, the zeroth-order condition is exactly the
statement `[L_a, R_b] = 0` for all `a, b ∈ 𝕆` — which, by the
non-vanishing associator, FAILS on the octonion factor.

This is the obstruction Bochniak-Sitarz identify (arXiv:2001.02613).

## What this file proves (Tier 1, structural)

* `commutator f g` is defined and unfolded.
* `ZerothOrder` and `OrderOne` are defined.
* The bridge:
  `ZerothOrder LeftMult RightMult ↔ ∀ a x b, L_a (R_b x) = R_b (L_a x)`
  (the natural commutation identity).

## References

* Connes, A., *Noncommutative Geometry* (1994), §VI.3 (zeroth-order),
  §VI.4 (order-one) axiom.
* Bochniak, A., Sitarz, A., *Spectral interaction between universes*,
  arXiv:2001.02613 — explicit obstruction analysis for non-associative
  spectra.
* Boyle, L., Farnsworth, S., *The standard model, the Pati-Salam model,
  and "Jordan geometry"*, arXiv:1910.11888.
-/

namespace SpectralPhysics.DixonOrderOne

open CayleyDickson

/-- The commutator of two endomorphisms of `OctonionFactor`:
`[f, g] x := f (g x) - g (f x)`. -/
def commutator (f g : OctonionFactor → OctonionFactor) :
    OctonionFactor → OctonionFactor :=
  fun x => f (g x) - g (f x)

theorem commutator_apply (f g : OctonionFactor → OctonionFactor) (x : OctonionFactor) :
    commutator f g x = f (g x) - g (f x) := rfl

/-- **Zeroth-order condition** (Connes 1994 §VI.3).

The representation `π` and its opposite `π'` commute pointwise:
`∀ a b, [π(a), π'(b)] = 0`.

This is necessary for the order-one axiom to be well-posed in the
standard NCG formalism. -/
def ZerothOrder
    (π π' : OctonionFactor → (OctonionFactor → OctonionFactor)) : Prop :=
  ∀ a b : OctonionFactor, commutator (π a) (π' b) = (fun _ => (0 : OctonionFactor))

/-- **Order-one condition** (Connes 1994 §VI.4).

For a Dirac-like operator `D`, `[D, π(a)]` commutes with `π'(b)`:
`∀ a b, [[D, π(a)], π'(b)] = 0`. -/
def OrderOne
    (D : OctonionFactor → OctonionFactor)
    (π π' : OctonionFactor → (OctonionFactor → OctonionFactor)) : Prop :=
  ∀ a b : OctonionFactor, commutator (commutator D (π a)) (π' b) = (fun _ => (0 : OctonionFactor))

/-! ## Zeroth-order specialisation to (LeftMult, RightMult) -/

/-- `ZerothOrder LeftMult RightMult` ⇔ `L_a (R_b x) = R_b (L_a x)`
for all `a, b, x`. -/
theorem zerothOrder_LeftMult_RightMult_iff :
    ZerothOrder LeftMult RightMult ↔
      ∀ a b x : OctonionFactor, LeftMult a (RightMult b x) = RightMult b (LeftMult a x) := by
  constructor
  · intro h a b x
    have h_ab := h a b
    have h_at_x := congrFun h_ab x
    -- commutator (LeftMult a) (RightMult b) x = LeftMult a (RightMult b x) - RightMult b (LeftMult a x) = 0
    simp only [commutator_apply] at h_at_x
    -- h_at_x : LeftMult a (RightMult b x) - RightMult b (LeftMult a x) = 0
    exact sub_eq_zero.mp h_at_x
  · intro hLR a b
    funext x
    simp only [commutator_apply]
    -- Goal: LeftMult a (RightMult b x) - RightMult b (LeftMult a x) = 0
    rw [hLR a b x, sub_self]

end SpectralPhysics.DixonOrderOne
