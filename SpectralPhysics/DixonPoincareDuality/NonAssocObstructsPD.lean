/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.DixonPoincareDuality.PoincareDualityAxiom

/-!
# Non-associativity obstructs Poincaré duality on the Dixon algebra

The K-theoretic intersection form of a real spectral triple
`(A, H, D, J, γ)` is constructed (Connes 1994 §VI.4) by composing
the algebra representation `π` with its opposite `π'` via the real
structure `J`. For the form to descend to a *well-defined* pairing
on K-theory classes — let alone to be non-degenerate — the two
actions must commute pointwise (the zeroth-order condition).

This commutation **fails** on the octonion factor `𝕆 = CD(ℍ)` of
the Dixon algebra: the non-associativity, witnessed via Cayley-
Dickson from `Quaternion ℝ`, gives explicit `a, b, x` with
`L_a (R_b x) ≠ R_b (L_a x)` (theorem
`LR_commutator_nonzero_witness` in
`DixonOrderOne.DixonAlgebra`).

Consequently, the K-theoretic intersection form on the canonical
Dixon-style carrier cannot land on the K-theory quotient: K-theory
itself, for a non-associative real algebra, is not the same object
as for an associative algebra — the category of finitely-generated
projective modules requires associativity to be well-defined. So
the Connes §VI.4 intersection form is not even well-posed on the
canonical Dixon triple.

This file packages that obstruction at the predicate level,
chained via the named axiom
`connes_PD_requires_wellDefinedness` introduced in `Verdict.lean`.

## What this file proves (Tier 1)

* `PD_implies_zerothOrder_canonical`:
  Given the standard reduction `PDImpliesWellDefined` for the
  canonical Dixon carrier, `PoincareDuality canonicalDixonTriple`
  forces `ZerothOrder LeftMult RightMult`.

* `PD_fails_for_canonical_dixon`:
  Under the standard reduction `PDImpliesWellDefined`, the
  canonical Dixon triple does NOT satisfy Poincaré duality.

* `PD_fails_for_dixon`:
  The headline conditional: under the same reduction, there is no
  abstract Dixon-style spectral triple that simultaneously
  matches the canonical `(LeftMult, RightMult)` actions AND
  satisfies Poincaré duality.

## Conditional structure (audit-honest)

The implication "Poincaré duality on the K-theory of a real
spectral triple ⇒ the intersection form descends to classes" is
the standard published reduction in Connes 1994 §VI.4. We carry it
as a predicate-level hypothesis (named `PDImpliesWellDefined`) in
`PoincareDualityAxiom.lean` and consume it once here.

The *Dixon-specific* obstruction — that `WellDefinedOnClasses`
fails on `canonicalDixonTriple` — is **unconditional Tier 1**
(`not_wellDefinedOnClasses_canonical_dixon`).

## References

* Connes, A., *Noncommutative Geometry* (1994), §VI.4.
* Bochniak, A., Sitarz, A., arXiv:2001.02613 §III — explicit
  treatment of K-theory non-degeneracy failure in the
  non-associative Dixon setting.
* Boyle, L., Farnsworth, S., arXiv:1910.11888.
-/

namespace SpectralPhysics.DixonPoincareDuality

open SpectralPhysics.DixonOrderOne

/-! ## PD-fail on the canonical Dixon triple -/

/-- **Tier 1 conditional.** Under the standard Connes §VI.4
reduction (`PDImpliesWellDefined`), if the canonical Dixon triple
satisfied Poincaré duality, then the zeroth-order commutation
`[LeftMult a, RightMult b] = 0` would hold for all `a, b`. -/
theorem PD_implies_zerothOrder_canonical
    (h_reduce : PDImpliesWellDefined canonicalDixonTriple) :
    PoincareDuality canonicalDixonTriple →
      ZerothOrder LeftMult RightMult := by
  intro h_pd
  have h_wd : WellDefinedOnClasses canonicalDixonTriple := h_reduce h_pd
  rw [wellDefinedOnClasses_canonical_iff_zerothOrder] at h_wd
  exact h_wd

/-- **Tier 1 conditional.** Under the standard Connes §VI.4
reduction, the canonical Dixon triple does NOT satisfy Poincaré
duality.

Proof: contrapositive of `PD_implies_zerothOrder_canonical`,
combined with the unconditional `not_zerothOrder_canonical_dixon`. -/
theorem PD_fails_for_canonical_dixon
    (h_reduce : PDImpliesWellDefined canonicalDixonTriple) :
    ¬ PoincareDuality canonicalDixonTriple := by
  intro h_pd
  exact not_zerothOrder_canonical_dixon
    (PD_implies_zerothOrder_canonical h_reduce h_pd)

/-! ## PD-fail at the existential level

Below we use the abbreviation `CanonicalDixonTriple` for a record
that recovers the canonical `(LeftMult, RightMult)` action data.
The point of the existential statement is that *any* extension of
the canonical algebra/opposite pair to a full Dixon-style triple
inherits the obstruction. -/

/-- An abstract spectral triple is **Dixon-canonical** if its
representation and opposite are exactly the canonical
left/right-multiplication actions on `𝕆`. -/
def IsCanonicalDixon (T : AbstractSpectralTriple) : Prop :=
  T.π = LeftMult ∧ T.π' = RightMult

/-- **Tier 1 conditional.**  Under the standard Connes §VI.4
reduction (applied uniformly), there is NO Dixon-canonical
abstract spectral triple `T` that satisfies Poincaré duality.

The named hypothesis is the *general* reduction
`PDImpliesWellDefined T`. The Dixon-specific obstruction is
unconditional. -/
theorem PD_fails_for_dixon
    (h_reduce : ∀ T : AbstractSpectralTriple,
        IsCanonicalDixon T → PDImpliesWellDefined T) :
    ¬ ∃ T : AbstractSpectralTriple,
        IsCanonicalDixon T ∧ PoincareDuality T := by
  rintro ⟨T, ⟨hπ, hπ'⟩, h_pd⟩
  -- The reduction applies because T is Dixon-canonical.
  have h_wd : WellDefinedOnClasses T := h_reduce T ⟨hπ, hπ'⟩ h_pd
  -- Unfold WellDefinedOnClasses with T.π = LeftMult, T.π' = RightMult
  -- to reach the zeroth-order predicate on (LeftMult, RightMult).
  apply not_zerothOrder_canonical_dixon
  rw [zerothOrder_LeftMult_RightMult_iff]
  intro a b x
  have h := h_wd a b x
  -- h : T.π a (T.π' b x) = T.π' b (T.π a x)
  rw [hπ, hπ'] at h
  exact h

end SpectralPhysics.DixonPoincareDuality
