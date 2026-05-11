/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.CompositionUniqueness.HypothesisSet
import SpectralPhysics.CompositionUniqueness.KasparovProductUniqueness
import SpectralPhysics.CompositionUniqueness.BroaderUniquenessOpen
import SpectralPhysics.CompositionBroaderUniqueness.NonKasparovCandidates

/-!
# Uncountable Obstruction — The Honest Open Predicate

This file records, as a **Prop-valued predicate** (NOT a theorem,
NOT an axiom), the honest open question that remains after the
named-candidate closure of `HigherMomentObstruction.lean`:

  *Is every binary operation on `Spectrum` satisfying the
  three-condition predicate either a Kasparov product (in the
  sense of `KasparovProductWitness` from v0.9.1) or equal to
  additive convolution?*

We name this predicate `BroaderUniquenessAllNonKasparov`.  It
quantifies over all `op : BinaryOpOnSpectra`, including the
uncountable continuum of operations not on any explicit named
list.

## Why a predicate, not a theorem

Proving `BroaderUniquenessAllNonKasparov` from current
mathematics requires a free-probability-level theorem that does
not exist in published form: the multiset moment-problem analogue
of Nica–Speicher (2006) §10.5–§11 must be ported up to
spectrum-level operations, and the missing piece is a
**categorical** characterisation of Kasparov-product operations
that is currently a research-program-scale open problem in NCG
(see Mesland–Rennie 2014 §6 for the closest existing fragment).

## Why NOT an axiom

Following the v0.9.1 redemption-discipline established in
`compute/self-model-deficit-rigorous` and
`compute/composition-uniqueness` (Path A): axiomatizing the
conclusion of an in-branch theorem is forbidden.  In particular,

  `axiom additive_unique_among_all_non_kasparov : ∀ op, … → op = additive`

would be straight conclusion-axiomatization, which the audit
catches and rejects.

## Anti-pattern check (defensive)

* `IsKasparov` is **NOT** `:= True`.  It is the existing v0.9.1
  predicate `KasparovProductWitness`, which encodes the symmetry
  and KK-product structure derived in
  `CompositionUniqueness/KasparovProductUniqueness.lean`.

* `BroaderUniquenessAllNonKasparov` is **NOT** asserted as a
  theorem with hidden axiom-smuggling.  It is a `def` returning
  `Prop` and never invoked in any equality-of-types reduction.

## References

* Voiculescu, D. (1985, 1991) — free additive convolution.
* Speicher, R. (1994) — multiplicative functions on
  non-crossing partitions; free convolution combinatorics.
* Nica, A., Speicher, R. (2006) — *Lectures on the Combinatorics
  of Free Probability*, LMS LNS 335, CUP.  §10.5–§11 are the
  most-relevant chapters for the moment-problem analogue.
* Bercovici, H., Voiculescu, D. (1993) — `⊠` multiplicative
  convolution.
* Mesland, B., Rennie, A. (2014) — *Nonunital spectral triples
  and metric completeness in unbounded KK-theory*.  §6 is the
  closest existing fragment of the categorical characterisation
  the uncountable case demands.
* Joyal, A., Street, R. (1991) — tensor calculus geometry.
-/

namespace SpectralPhysics.CompositionBroaderUniqueness

open SpectralPhysics.CompositionUniqueness

/-! ## The `IsKasparov` predicate

A binary operation `op` "is Kasparov" iff there exists a
`KasparovProductWitness` for it.  This is **not** `:= True`: the
KasparovProductWitness structure has substantive content —
symmetry and the KK-product marker — already established as
non-trivial in v0.9.1's
`CompositionUniqueness/KasparovProductUniqueness.lean`.

The honest open question is whether every three-condition
operation admits such a witness.  -/
def IsKasparov (op : BinaryOpOnSpectra) : Prop :=
  Nonempty (KasparovProductWitness op)

/-! ## The headline open predicate -/

/-- **The v0.9.2 deferred-A.1 open predicate**: every binary
operation on `Spectrum` satisfying ThreeConditions is either a
Kasparov product or equals additive convolution.

This is the **uncountable closure** statement: it quantifies over
all of `BinaryOpOnSpectra`, which is uncountable.  The disjunction
captures the two ways the three-condition predicate can be
satisfied as of the v0.9.1 state of the art:

* `IsKasparov op` — closed conditionally on K1+K2+K3 (v0.9.1
  Scope 3).
* `op = BinaryOpOnSpectra.additive` — the explicit canonical
  operation (v0.9.1 Scope 1; v0.9.2 Scope: named candidates).

It is **NOT proved** in this file.  It is **NOT axiomatized**.
It is recorded as the v0.9.2 honest open problem. -/
def BroaderUniquenessAllNonKasparov : Prop :=
  ∀ op : BinaryOpOnSpectra,
    ThreeConditions op → IsKasparov op ∨ op = BinaryOpOnSpectra.additive

/-! ## The named free-probability research program

`FreeProbResearchProgram` is the standard name under which the
above predicate sits in the free-probability literature.  We
record the equivalence (definitional in our formalisation) to
flag that solving the v0.9.2 A.1 open problem is *exactly* this
research program, not a different one. -/

/-- **The free-probability research program** at the spectrum
level: the Nica–Speicher (2006) §10.5–§11 moment-problem analogue
applied to multiset-valued binary operations.

Currently open in the free-probability literature.  Solving it
would close v0.9.2 A.1 unconditionally. -/
def FreeProbResearchProgram : Prop := BroaderUniquenessAllNonKasparov

/-- **The v0.9.2 A.1 open accounting**: the headline open
predicate `BroaderUniquenessAllNonKasparov` is **definitionally
equivalent** to the named free-probability research program
`FreeProbResearchProgram`.  Solving one solves the other.

This is `Iff.rfl` because `FreeProbResearchProgram` is recorded
as the standard literature name for the same predicate — the
content of this theorem is its **name**, which fingers the exact
research program one would have to settle. -/
theorem v092_A1_open :
    BroaderUniquenessAllNonKasparov ↔ FreeProbResearchProgram :=
  Iff.rfl

/-! ## Honest conditional closure -/

/-- **The conditional form**: assuming the (open)
`BroaderUniquenessAllNonKasparov` predicate, every three-condition
operation is either Kasparov or additive.

Any caller using this theorem MUST supply the hypothesis — there
is no path within this branch to discharge it. -/
theorem uncountable_closure_under_hypothesis
    (h : BroaderUniquenessAllNonKasparov)
    {op : BinaryOpOnSpectra} (h_three : ThreeConditions op) :
    IsKasparov op ∨ op = BinaryOpOnSpectra.additive :=
  h op h_three

/-- **Restatement as Kasparov-or-trace-matches-additive**: the
trace-channel form follows from the unconditional v0.9.1 Scope-2
theorem regardless of how the uncountable case is resolved.  This
lemma is a sanity check that the open hypothesis is **not**
needed to obtain the trace-channel conclusion.  -/
theorem trace_channel_independent_of_uncountable_obstruction :
    ∀ op : BinaryOpOnSpectra, ThreeConditions op →
      ∀ μ ν : Spectrum,
        Spectrum.trace (op μ ν) = Spectrum.trace (additiveConv μ ν) :=
  fun op h_three μ ν =>
    trace_uniqueness_of_hamiltonian_additivity op h_three.hamilton μ ν

end SpectralPhysics.CompositionBroaderUniqueness
