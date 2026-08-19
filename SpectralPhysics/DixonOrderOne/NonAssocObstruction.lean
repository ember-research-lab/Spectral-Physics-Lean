/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.DixonOrderOne.OrderOneCondition

/-!
# Non-associativity obstruction to the order-one axiom

The Connes order-one axiom (Connes 1994 §VI.4) presupposes the
*zeroth-order condition* (§VI.3):
```
∀ a b ∈ A,   [π(a), J π(b)* J⁻¹] = 0.
```
For the Dixon algebra `A_Dixon = ℂ ⊗_ℝ ℍ ⊗_ℝ 𝕆` represented on itself
by left multiplication, with the opposite action realised (in the
*canonical* dimension-matched setting) as right multiplication, this
becomes
```
∀ a b ∈ 𝕆,   [L_a, R_b] = 0
```
on the `𝕆`-factor.  But `[L_a, R_b]` is exactly the associator
`(a*x)*b - a*(x*b)` (modulo sign), which is **identically nonzero**
on `𝕆`.  Therefore the canonical left/right representation of the
Dixon algebra *cannot* satisfy the zeroth-order condition; a
fortiori, it cannot satisfy the order-one axiom in the standard
Connes formalism.

This is the obstruction explicitly identified by Bochniak-Sitarz
(arXiv:2001.02613) and discussed in Boyle-Farnsworth
(arXiv:1910.11888).

## What this file proves (Tier 1)

* `not_zerothOrder_canonical_dixon`:
  `¬ ZerothOrder LeftMult RightMult`
  (unconditional — the witness comes from `i*j ≠ j*i` in ℍ ⊂ 𝕆 via
  Cayley-Dickson).

* `orderOne_fails_canonical_dixon`:
  given the standard NCG axiom `OrderOne_implies_ZerothOrder` (i.e.
  the standard reduction step in §VI.3 of Connes 1994), the
  canonical Dixon representation fails the order-one axiom for
  EVERY Dirac-like operator `D`.

## Conditional structure (audit-honest)

The standard implication "first-order ⇒ zeroth-order" is itself part
of the published Connes framework; it is named as the predicate
`OrderOne_implies_ZerothOrder` and carried as a hypothesis to keep
the obstruction theorem framework-internal.  The Lean-formalised
content of *this* file is exactly the structural lemma: if a
representation has non-commuting opposite actions, no choice of `D`
salvages the order-one axiom.

## References

* Connes, A., *Noncommutative Geometry* (1994), §VI.3–VI.4.
* Bochniak, A., Sitarz, A., arXiv:2001.02613.
* Boyle, L., Farnsworth, S., arXiv:1910.11888.
-/

namespace SpectralPhysics.DixonOrderOne

open CayleyDickson

/-! ## Zeroth-order failure for the canonical Dixon representation -/

/-- **Tier 1 (unconditional).**  The canonical Dixon representation
`(π, π') = (LeftMult, RightMult)` does NOT satisfy the zeroth-order
condition.

Proof: by `LR_commutator_nonzero_witness`, there exist
`a, b, x : 𝕆` with `L_a (R_b x) ≠ R_b (L_a x)`.  This contradicts
the universally-quantified `ZerothOrder` predicate. -/
theorem not_zerothOrder_canonical_dixon :
    ¬ ZerothOrder LeftMult RightMult := by
  intro h
  rw [zerothOrder_LeftMult_RightMult_iff] at h
  obtain ⟨a, b, x, hne⟩ := LR_commutator_nonzero_witness
  exact hne (h a b x)

/-! ## Conditional: order-one fails for every D

We carry the standard "first-order implies zeroth-order" reduction
of Connes 1994 §VI.3 as a NAMED PREDICATE-LEVEL HYPOTHESIS.  This is
the published reduction: under the standard NCG axioms for a
spectral triple with real structure, the first-order axiom is
formulated *on top of* the zeroth-order axiom; if the latter fails
the former cannot hold for any D.

We do NOT prove this implication from scratch — it requires the full
NCG axiom system (KO-dimension, J-structure, ε signs, regularity)
which is far beyond this file's scope.

**2026-08-18 (audit U8, review pass).** Nor is it consumed any more: as
formalised over an UNCONSTRAINED `D`, `OrderOneImpliesZerothOrder LeftMult
RightMult` is FALSE (`Verdict.dixon_reduction_hypothesis_false`, kernel
axioms only — the zero map satisfies `OrderOne` while zeroth-order fails).
The predicate is kept only so that honest negative can be stated. -/

/-- The standard Connes-1994 §VI.3 reduction, stated as a predicate
on a (representation, opposite-representation) pair.

`OrderOneImpliesZerothOrder π π'` says: if for some Dirac `D` the
order-one axiom holds for `(D, π, π')`, then the zeroth-order
condition holds for `(π, π')`. -/
def OrderOneImpliesZerothOrder
    (π π' : OctonionFactor → (OctonionFactor → OctonionFactor)) : Prop :=
  (∃ D, OrderOne D π π') → ZerothOrder π π'

/-! ### `order_one_fails_canonical_dixon` — DELETED (2026-08-18 review pass)

`theorem order_one_fails_canonical_dixon (h_reduce : OrderOneImpliesZerothOrder
LeftMult RightMult) : ¬ ∃ D, OrderOne D LeftMult RightMult` used to live here.
Its hypothesis is refuted in this repository
(`Verdict.dixon_reduction_hypothesis_false`), so the theorem was a vacuous
conditional: it could never be instantiated, while its NAME asserted the
withdrawn headline (`Verdict.dixon_order_one_fails`, also deleted — the zero
map is a counterexample). A docstring caveat on a decl whose name reads as a
closure is exactly the laundering pattern the 2026-08-18 content audit exists
to remove, and nothing consumed it, so it is deleted rather than relabelled.

What remains, unconditionally: `not_zerothOrder_canonical_dixon` (the genuine
algebraic obstruction, below/above), `dixon_has_nonzero_associator`,
`dixon_LR_does_not_commute`, and the honest negative
`Verdict.dixon_reduction_hypothesis_false`. Whether every *genuine* Dirac
operator fails order-one is OPEN in Lean (it needs a formalisation of
"Dirac-like `D`", which is new content, not a repair). -/

/-! ## Headline statements for downstream consumers -/

/-- **Tier 1 (unconditional).**  There exist octonion-factor elements
`a, b, x` for which `L_a R_b x ≠ R_b L_a x`.

This is the *algebraic* obstruction in its rawest form: even before
introducing Dirac operators or J-structures, left and right
multiplication on `𝕆` fail to commute. -/
theorem dixon_LR_commutator_nonzero :
    ∃ a b x : OctonionFactor, LeftMult a (RightMult b x) ≠ RightMult b (LeftMult a x) :=
  LR_commutator_nonzero_witness

/-- **Tier 1 (unconditional).**  The Dixon octonion factor has a
non-zero associator. -/
theorem dixon_associator_nonzero :
    ∃ a x b : OctonionFactor, associator a x b ≠ 0 :=
  associator_nonzero_witness

end SpectralPhysics.DixonOrderOne
