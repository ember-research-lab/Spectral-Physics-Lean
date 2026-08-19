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
opposite acts by right multiplication, fails the **zeroth-order**
condition unconditionally.

**2026-08-18 content repair (audit U8):** the previous headline "fails the
order-one axiom for every choice of Dirac operator `D`" is WITHDRAWN as
formalised — with `D` unconstrained the zero map satisfies `OrderOne`
(`zero_map_orderOne`), and the named axiom that bridged order-one to
zeroth-order was compile-verified UNSOUND and removed. See the section
"The former named axiom" below and `STATUS.md` §0.

## Named axiom

None (since 2026-08-18). The module now proves
`dixon_reduction_hypothesis_false : ¬ OrderOneImpliesZerothOrder LeftMult RightMult`
on kernel axioms only.

The Dixon-specific obstruction (`not_zerothOrder_canonical_dixon`)
is **unconditional** (Tier 1) and provided in
`NonAssocObstruction.lean`.

## Audit-honest framing

* The integer "obstruction lives" is NOT used as a numerical anchor.
* No named axiom remains; the Connes / Bochniak-Sitarz reduction is
  cited as literature context only, not consumed.
* The verdict on the *zeroth-order* condition is NEGATIVE (NO closure)
  and unconditional; the *order-one* verdict is OPEN in Lean.

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

/-! ## The former named axiom — REMOVED 2026-08-18 (compile-verified UNSOUND, audit U8)

`axiom bochniak_sitarz_zerothOrder_reduction : OrderOneImpliesZerothOrder LeftMult RightMult`
used to live here, cited as the Connes 1994 §VI.3 / Bochniak–Sitarz reduction. As formalised —
`(∃ D, OrderOne D LeftMult RightMult) → ZerothOrder LeftMult RightMult` over an UNCONSTRAINED
`D : 𝕆 → 𝕆` — it is **false**: the zero map satisfies `OrderOne` vacuously
(`zero_map_orderOne` below), so the axiom forced `ZerothOrder LeftMult RightMult`, which
`not_zerothOrder_canonical_dixon` refutes. Hostile witness compiled to `False`:
`spectral_physics/lean-content-audit-2026-08-18/DixonU8False.lean` (manuscript repo).

The published reduction is a statement about genuine Dirac operators inside the full
real-spectral-triple axiomatics; the predicate `OrderOne` here carries none of that structure,
so no citation can license the unconstrained implication. Constraining `D` would be new
mathematical content (which conditions a "Dirac-like" `D` must satisfy), outside a
labels-and-soundness repair — the honest negative is recorded instead. -/

/-- The zero map satisfies the (unconstrained) order-one predicate for the canonical
Dixon representation: both nested commutators collapse because `L_a 0 = 0 = R_b 0`. -/
theorem zero_map_orderOne : OrderOne (fun _ => (0 : OctonionFactor)) LeftMult RightMult := by
  intro a b
  funext x
  simp [commutator_apply, LeftMult, RightMult]

/-- **Honest negative (Tier 1, kernel axioms only).** The reduction hypothesis
`OrderOneImpliesZerothOrder LeftMult RightMult`, as formalised over unconstrained `D`, is
FALSE. This is what refuted the former named axiom; it is also why the vacuous
conditional `order_one_fails_canonical_dixon` was deleted from
`NonAssocObstruction.lean` (its hypothesis is never satisfiable). -/
theorem dixon_reduction_hypothesis_false :
    ¬ OrderOneImpliesZerothOrder LeftMult RightMult :=
  fun h => not_zerothOrder_canonical_dixon (h ⟨_, zero_map_orderOne⟩)

/-! ## Headline verdict theorem -/

/-- **Verdict — WITHDRAWN as formalised (2026-08-18).** The former headline
`dixon_order_one_fails : ¬ ∃ D, OrderOne D LeftMult RightMult` is FALSE in this
formalisation: the zero map is a witness (`zero_map_orderOne`). What remains proved,
unconditionally: the canonical Dixon representation fails the *zeroth-order* condition
(`not_zerothOrder_canonical_dixon`), the associator is non-zero
(`dixon_has_nonzero_associator`), and `L_a`, `R_b` do not commute
(`dixon_LR_does_not_commute`). Whether every *genuine* Dirac operator (a `D` with the
structure the NCG axioms require — not formalised here) fails order-one is OPEN in Lean;
the v0.9 line 6731 negative resolution therefore rests on the zeroth-order obstruction plus
the *unformalised* published reduction, not on a Lean theorem about `D`. -/
theorem dixon_order_one_unconstrained_has_witness :
    ∃ D : OctonionFactor → OctonionFactor, OrderOne D LeftMult RightMult :=
  ⟨_, zero_map_orderOne⟩

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
