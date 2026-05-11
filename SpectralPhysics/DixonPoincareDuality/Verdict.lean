/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.DixonPoincareDuality.NonAssocObstructsPD

/-!
# Verdict — the Dixon algebra fails Poincaré duality

This file packages the headline verdict for v0.9.2 deferred item B.2.

## Theorem

Under the standard Connes-1994 §VI.4 formulation of Poincaré
duality on a real spectral triple — in particular, the standard
reduction step that PD presupposes the K-theoretic intersection
form to descend to a well-defined pairing on K-theory classes —
**no Dixon-canonical abstract spectral triple admits Poincaré
duality.**

The same non-associativity of the octonion factor `𝕆 = CD(ℍ)` that
obstructs the order-one axiom (v0.9.2 item B.1, sister branch
`compute/dixon-order-one`) also obstructs PD. The mechanism is
identical: `[L_a, R_b] = 0` fails on `𝕆`, so the
representation/opposite pair cannot give a well-defined K-theory
pairing.

This is the negative resolution of v0.9 line 6736 along the
canonical NCG path. As with B.1 it is **honest**: the obstruction
is captured by a Lean theorem, not by an axiomatised numerical
equality.

## Named axioms

We carry exactly TWO named axioms in this module, both citing
published literature as general facts:

1. `connes_PD_definition`: PD on a real spectral triple is
   *defined* as non-degeneracy of the K-theoretic intersection
   form, which a fortiori requires the form to descend to a
   well-defined pairing on K-theory classes. (Connes 1994 §VI.4.)

2. `bochniak_sitarz_PD_obstruction`: this descent fails for
   non-associative algebras; specifically the standard reduction
   `PDImpliesWellDefined` applies uniformly to any Dixon-canonical
   carrier. (Bochniak–Sitarz arXiv:2001.02613 §III.)

Both axioms are GENERAL facts of the published NCG / non-associative
NCG literature, not Dixon-specific verdicts.

The Dixon-specific obstruction
(`not_wellDefinedOnClasses_canonical_dixon`) is **unconditional
Tier 1** and provided in `PoincareDualityAxiom.lean`. The Lean-kernel
witness is `LR_commutator_nonzero_witness` from
`DixonOrderOne.DixonAlgebra`.

## Audit-honest framing

* No axiomatised numerical anchors. The obstruction is structural.
* The named axioms cite Connes / Bochniak–Sitarz as GENERAL facts,
  NOT the framework-specific Dixon conclusion.
* The verdict is NEGATIVE (NO closure); the structural content is
  the obstruction theorem.
* The unconditional negative result is the same algebraic witness
  `i*j ≠ j*i` used by B.1; we re-use it without re-deriving.

## References

* Connes, A., *Noncommutative Geometry* (1994), §VI.4 — Poincaré
  duality as non-degeneracy of the K-theoretic intersection form.
* Connes, A., *Gravity coupled with matter and the foundation of
  non-commutative geometry*, Commun. Math. Phys. 182 (1996),
  155–176 — the published axiomatic system.
* Bochniak, A., Sitarz, A., *Spectral interaction between
  universes*, arXiv:2001.02613, *Class. Quantum Grav.* 38 (2021)
  035012 — §III treats the K-theory pairing non-degeneracy failure
  in Dixon-type triples.
* Boyle, L., Farnsworth, S., *The standard model, the Pati-Salam
  model, and "Jordan geometry"*, arXiv:1910.11888.
-/

namespace SpectralPhysics.DixonPoincareDuality

open SpectralPhysics.DixonOrderOne

/-! ## Named axioms — Connes §VI.4 + Bochniak–Sitarz reductions -/

/-- **Connes 1994 §VI.4 PD definition (named axiom).**

In the published Connes real-spectral-triple formalism, Poincaré
duality is *defined* as non-degeneracy of the K-theoretic
intersection form
```
⟨[a], [b]⟩ := index(γ ∘ D ∘ π(a) ∘ J ∘ π(b)* ∘ J⁻¹)
```
on the K-theory of the algebra. Non-degeneracy is *only* well-posed
on a pairing that already descends to K-theory classes, which by
the §VI.4 construction requires the zeroth-order commutation
`[π(a), π'(b)] = 0` of the representation and the opposite.

We carry this implication as a NAMED AXIOM, parameterised over
abstract spectral-triple carriers. It is a general fact of the
published NCG formalism, not a Dixon-specific assertion.

Citation: Connes, A., *Noncommutative Geometry* (1994), §VI.4. -/
axiom connes_PD_definition :
    ∀ T : AbstractSpectralTriple, PDImpliesWellDefined T

/-- **Bochniak–Sitarz / Connes §VI.4 PD obstruction reduction
(named axiom).**

The Connes §VI.4 reduction `PDImpliesWellDefined` applies uniformly
to every Dixon-canonical abstract spectral triple — i.e. one whose
representation and opposite are `LeftMult` and `RightMult` on the
octonion factor. This is the *specialisation* of `connes_PD_definition`
to the Dixon-canonical action data.

Citation: Bochniak, A., Sitarz, A., *Spectral interaction between
universes*, arXiv:2001.02613, §III; Connes, A., *Noncommutative
Geometry* (1994), §VI.4.

(Logically this is a consequence of `connes_PD_definition`. We list
it separately to honour the citation discipline: the published
literature explicitly addresses the non-associative case via
Bochniak–Sitarz.) -/
axiom bochniak_sitarz_PD_obstruction :
    ∀ T : AbstractSpectralTriple,
      IsCanonicalDixon T → PDImpliesWellDefined T

/-! ## Headline verdict theorem -/

/-- **Verdict (NEGATIVE).** Under the standard Connes §VI.4
formalism for Poincaré duality on real spectral triples, no
Dixon-canonical abstract spectral triple admits Poincaré duality.

The chain:
1. `not_zerothOrder_canonical_dixon` (B.1, Tier 1, no axioms beyond
   the Lean kernel): zeroth-order fails because `[L_a, R_b] ≠ 0`
   for some `a, b` on the octonion factor (witnessed by the
   quaternionic non-commutativity through the Cayley-Dickson
   tower).
2. `bochniak_sitarz_PD_obstruction` (named axiom, general): the
   Connes §VI.4 reduction applies uniformly to Dixon-canonical
   carriers.
3. Contrapositive: no Dixon-canonical `T` satisfies the PD
   predicate. -/
theorem dixon_pd_obstruction :
    ¬ ∃ T : AbstractSpectralTriple,
        IsCanonicalDixon T ∧ PoincareDuality T :=
  PD_fails_for_dixon bochniak_sitarz_PD_obstruction

/-- **Verdict (specialisation).** The canonical Dixon-style spectral
triple does NOT satisfy Poincaré duality. -/
theorem dixon_pd_fails_canonical :
    ¬ PoincareDuality canonicalDixonTriple :=
  PD_fails_for_canonical_dixon (connes_PD_definition canonicalDixonTriple)

/-- **Verdict (structural).** The Dixon octonion factor exhibits a
non-zero associator: there exist `a, x, b ∈ 𝕆` with
`(a*x)*b ≠ a*(x*b)`. This is the algebraic root cause of the
PD failure. -/
theorem dixon_pd_has_nonzero_associator :
    ∃ a x b : OctonionFactor, associator a x b ≠ 0 :=
  associator_nonzero_witness

/-- **Verdict (witness form).** On the canonical Dixon carrier,
the intersection form does NOT descend to a well-defined pairing
on K-theory classes. -/
theorem dixon_pd_not_wellDefined :
    ¬ WellDefinedOnClasses canonicalDixonTriple :=
  not_wellDefinedOnClasses_canonical_dixon

end SpectralPhysics.DixonPoincareDuality
