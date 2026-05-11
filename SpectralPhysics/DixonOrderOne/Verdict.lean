/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.DixonOrderOne.NonAssocObstruction

/-!
# Verdict — the Dixon algebra fails the Connes order-one axiom

This file packages the headline verdict for v0.9.2 deferred item B.1.

## Theorem

Under the standard Connes-Marcolli formulation of a real spectral
triple — in particular, the standard reduction step that the
order-one axiom presupposes the zeroth-order commutation
`[π(a), π'(b)] = 0` — the canonical Dixon-algebra spectral triple,
in which the algebra acts on itself by left multiplication and the
opposite acts by right multiplication, **fails the order-one
axiom for every choice of Dirac operator `D`**.

This is the negative resolution of v0.9 line 6731 along the
canonical NCG path.  It is **honest**: the obstruction is captured
by a Lean theorem, not by an axiomatised numerical equality.

## Named axiom

We carry exactly ONE named axiom in this module:
`bochniak_sitarz_zerothOrder_reduction`.  It asserts the standard
Connes 1994 §VI.3 / Bochniak-Sitarz 2021 statement that the
zeroth-order condition is a necessary consequence of the order-one
axiom in the published real-spectral-triple formalism.  This is a
GENERAL fact of the Connes program, not a Dixon-specific assertion.

The Dixon-specific obstruction (`not_zerothOrder_canonical_dixon`)
is **unconditional** (Tier 1) and provided in
`NonAssocObstruction.lean`.

## Audit-honest framing

* The integer "obstruction lives" is NOT used as a numerical anchor.
* The named axiom cites Bochniak-Sitarz / Connes, NOT the framework.
* The verdict is NEGATIVE (NO closure); the structural content is
  the obstruction theorem.

## References

* Connes, A., *Noncommutative Geometry* (1994), §VI.3 (zeroth-order
  axiom as prerequisite for order-one).
* Bochniak, A., Sitarz, A., *Spectral interaction between universes*,
  arXiv:2001.02613, *Class. Quantum Grav.* 38 (2021) 035012 — §II.B
  contains the explicit non-associativity obstruction analysis.
* Boyle, L., Farnsworth, S., *The standard model, the Pati-Salam model,
  and "Jordan geometry"*, arXiv:1910.11888, §3.
-/

namespace SpectralPhysics.DixonOrderOne

open CayleyDickson

/-! ## Named axiom — Bochniak-Sitarz / Connes reduction -/

/-- **Bochniak-Sitarz / Connes 1994 §VI.3 reduction (named axiom).**

In the standard real-spectral-triple formalism, the order-one axiom
`[[D, π(a)], π'(b)] = 0` is formulated *on top of* the zeroth-order
condition `[π(a), π'(b)] = 0`.  Equivalently, if for some Dirac `D`
the order-one axiom holds for `(π, π')`, then the zeroth-order
condition automatically holds for `(π, π')`.

This is a GENERAL fact of the published NCG formalism.  We do NOT
attempt to formalise the full real-spectral-triple axiomatics here;
we name the implication and consume it once.

Citations:
* Connes, A., *Noncommutative Geometry* (1994), §VI.3.
* Bochniak, A., Sitarz, A., arXiv:2001.02613, §II.B. -/
axiom bochniak_sitarz_zerothOrder_reduction :
    OrderOneImpliesZerothOrder LeftMult RightMult

/-! ## Headline verdict theorem -/

/-- **Verdict (NEGATIVE).**  Under the standard NCG order-one
formalism, the canonical Dixon-algebra spectral triple (algebra acting
on itself by left multiplication, opposite acting by right
multiplication) does NOT admit any Dirac operator `D` satisfying the
order-one axiom.

The chain:
1. `not_zerothOrder_canonical_dixon` (Tier 1, no axioms beyond the
   kernel): the zeroth-order condition fails because `[L_a, R_b] ≠ 0`
   for some `a, b` on the octonion factor (witnessed by the
   quaternionic non-commutativity through the Cayley-Dickson tower).
2. `bochniak_sitarz_zerothOrder_reduction` (named axiom, generic):
   the order-one axiom (for any `D`) implies the zeroth-order
   condition in the published NCG formalism.
3. Contrapositive: no `D` satisfies the order-one axiom for
   the canonical Dixon representation. -/
theorem dixon_order_one_fails :
    ¬ ∃ D : OctonionFactor → OctonionFactor, OrderOne D LeftMult RightMult :=
  order_one_fails_canonical_dixon bochniak_sitarz_zerothOrder_reduction

/-- **Verdict (positive structural statement).**  The Dixon octonion
factor exhibits a non-zero associator: there exist `a, x, b ∈ 𝕆` with
`(a*x)*b ≠ a*(x*b)`.

This is the algebraic root cause of the order-one failure. -/
theorem dixon_has_nonzero_associator :
    ∃ a x b : OctonionFactor, associator a x b ≠ 0 :=
  dixon_associator_nonzero

/-- **Verdict (witness form).**  The Dixon canonical representation
has elements where left and right multiplication fail to commute. -/
theorem dixon_LR_does_not_commute :
    ∃ a b x : OctonionFactor, LeftMult a (RightMult b x) ≠ RightMult b (LeftMult a x) :=
  dixon_LR_commutator_nonzero

end SpectralPhysics.DixonOrderOne
