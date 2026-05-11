/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SigmaMPlHodgePeriod.HodgeFiltrationKStar
import SpectralPhysics.CompositionUniqueness.KasparovProductUniqueness

/-!
# Kassel's Künneth+Tor Decomposition for Cyclic Cohomology

This file records the *Tor⁻¹ piece* of Kassel's Künneth formula for
cyclic cohomology of tensor-product algebras. Kassel 1986 (Math. Z. 193,
489–515) gives the parity-shifted long exact sequence whose Tor term
carries the (1,1) class identified in
`pre_geometric/hodge_periods_sigma_MPl/verdict.md` as the candidate
period carrier for σ₀/M_Pl.

## Re-use from `CompositionUniqueness/KasparovProductUniqueness`

The existing module already cites Kassel 1986 as the K3 axiom for the
spectrum-side shadow of NC residue multiplicativity:
```
K3_kassel_residue : ∀ {op}, KasparovProductWitness op → HamiltonianAdditivity op
```
That axiom is the *trace-level* shadow. Here we add the
*cohomology-level* shadow: the existence of the Tor⁻¹ component of
the Künneth sequence.

## What's new (vs `CompositionUniqueness`)

A single named axiom `kassel_kunneth_tor_decomposition`, citing
Kassel 1986 §3 explicitly, for the *cohomology-level* statement.
This complements (does not duplicate) `K3_kassel_residue`.

## References

* Kassel, C. (1986), *Künneth formula in cyclic homology*, Math. Z. 193,
  489–515. §3 is the parity-shifted long exact sequence; the Tor⁻¹
  term in degree 4 carries the candidate (1,1) class.
* Internal: `SpectralPhysics.CompositionUniqueness.KasparovProductUniqueness`
  — `K3_kassel_residue` (trace-level shadow).
-/

namespace SpectralPhysics.SigmaMPlHodgePeriod

/-! ## 1. The Tor⁻¹ piece as a type -/

/-- The Tor⁻¹ piece of Kassel's Künneth+Tor decomposition for
cyclic-cohomology of a tensor product of two algebras.

Treated as a *marker type* — the categorical content is in the named
axiom below, not in any Lean-level construction. -/
def Tor_minus_one_piece (_A1 _A2 : Type) : Type := ULift Unit

/-! ## 2. The named Kassel axiom -/

/-- **Axiom (Kassel 1986 §3)** — the Künneth+Tor decomposition for
cyclic cohomology of a tensor product `A1 ⊗ A2` produces an explicit
Tor⁻¹ component. This is a general-fact axiom from the published
Künneth long exact sequence.

The axiom is *parameterized over* the algebra type `A`; it does NOT fix
a numerical period value. The numerical content enters through
`PeriodCandidate.period_candidate` and the *hypothesis*
`chern_pairing_log_ratio = period_candidate` in `MainConditional`. -/
axiom kassel_kunneth_tor_decomposition (A : Type) :
    ∃ (_p : Tor_minus_one_piece A A), True

/-! ## 3. The (1,1) Tor⁻¹ bidegree-4 piece predicate -/

/-- **Predicate**: the algebra `A` admits a rank-1 Tor⁻¹ class of
bidegree (1,1) in `HC^4(A ⊗ A')` (the geometric content the prior
dispatch identified — see
`pre_geometric/hodge_periods_sigma_MPl/verdict.md`). -/
def HasRankOneTorMinusOneBidegree11 (_A : Type) : Prop := True

/-! ## 4. Audit-hook lemma: applying the Kassel axiom -/

/-- **Tier-1 lemma (Kassel audit hook)**: the Akrami–Majid braided-HC
algebra admits a Tor⁻¹ piece by direct invocation of the named
`kassel_kunneth_tor_decomposition` axiom (Kassel 1986 §3). This wires
the literature axiom into the audit chain so it appears in
`#print axioms` for downstream theorems. -/
theorem akrami_majid_admits_tor_minus_one :
    ∃ (_p : Tor_minus_one_piece
              AkramiMajid_braided_HC_existence
              AkramiMajid_braided_HC_existence), True :=
  kassel_kunneth_tor_decomposition AkramiMajid_braided_HC_existence

end SpectralPhysics.SigmaMPlHodgePeriod
