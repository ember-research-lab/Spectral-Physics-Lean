/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.CompositionUniqueness.HypothesisSet
import SpectralPhysics.CompositionUniqueness.AdditiveSatisfies
import SpectralPhysics.CompositionUniqueness.Theorem
import SpectralPhysics.CompositionBroaderUniqueness.NonKasparovCandidates
import SpectralPhysics.CompositionBroaderUniqueness.TraceLevelDistinction

/-!
# Higher-Moment Obstruction — Closure Among the Four Named
  Non-Kasparov Candidates

This file states and proves the load-bearing **Tier-1** conditional
closure theorem for the v0.9.2 A.1 deferred item: among the four
**named** non-Kasparov factorization candidates from
`NonKasparovCandidates.lean`, the three-condition predicate
selects exactly the additive operation.

## The theorem (Scope: named-candidate closure)

`broader_uniqueness_among_named_candidates`:

  Let `op : BinaryOpOnSpectra` be such that:

  (1) `op = freeVoiculescuConv` or `multFreeConv` or
      `monoidalNonKConv` or `boxedConv 1`  *(boxed at the
      explicit `a = 1` witness)*  or `additive` itself; and
  (2) `op` satisfies the three-condition predicate.

  Then `op = additive`.

## What this theorem closes

Closes **closure against the named non-Kasparov candidates** at the
spectrum-level shadow.  Each of the three genuine non-Kasparov
shadows (free, multiplicative-free, monoidal-non-K) is ruled out
by `TraceLevelDistinction.lean` (each fails Hamiltonian
additivity on an explicit witness pair, hence cannot satisfy
ThreeConditions).  The boxed family is closed at `a = 1`; for
other `a` values see the open-content predicate in
`UncountableObstruction.lean`.

## What this theorem does NOT close

* **Other values of `a ∈ (0, 1)`** for `boxedConv`.  Each interior
  `a` requires its own witness; the trace-level mismatch grows
  with `a`, but Lean does not (and need not) iterate over the
  uncountable parameter range here.
* **Other non-Kasparov factorizations not in the named list.**
  This is the uncountable-closure problem, recorded in
  `UncountableObstruction.lean` as a `Prop` predicate identified
  as a free-probability research program (Nica–Speicher 2006).

## References

* v0.9.1: `CompositionUniqueness/Theorem.lean` —
  `three_conditions_force_trace_law` (zero-axiom Scope-2 result).
* v0.9.1: `BroaderUniquenessOpen.lean` — open predicate for the
  uncountable closure.
* Voiculescu (1985, 1991); Speicher (1994); Nica–Speicher (2006).
-/

namespace SpectralPhysics.CompositionBroaderUniqueness

open SpectralPhysics.CompositionUniqueness

/-! ## The named-candidate enumeration

A `Prop`-bearing enumeration: the operation `op` belongs to the
explicit named-candidate list.  We restrict the boxed candidate to
the specific witness parameter `a = 1` at which
`boxed_violates_hamiltonian_additivity` provides Tier-1 closure.
-/

/-- The named-candidate set: additive, free, mult-free,
monoidal-non-K, or boxed-at-`a=1`.  An operation `op` "is named"
iff it equals one of these five shadows pointwise. -/
def IsNamedCandidate (op : BinaryOpOnSpectra) : Prop :=
  op = BinaryOpOnSpectra.additive ∨
  op = ⟨freeVoiculescuConv⟩ ∨
  op = ⟨multFreeConv⟩ ∨
  op = ⟨monoidalNonKConv⟩ ∨
  op = ⟨boxedConv 1⟩

/-! ## Headline conditional closure (Tier 1, zero new axioms beyond
v0.9.1's K-axioms / Minkowski axioms) -/

/-- **The Tier-1 headline of `CompositionBroaderUniqueness`**:
among the four named non-Kasparov candidates plus `additive`
itself, the three-condition predicate selects `additive`.

This is the **conditional closure**:

  *Given* (a) `op` is in the named-candidate list and
  (b) `op` satisfies ThreeConditions, *then* `op = additive`.

The proof simply enumerates the five disjuncts and disposes of the
four non-additive ones via the Tier-1 falsifiers from
`TraceLevelDistinction.lean`. -/
theorem broader_uniqueness_among_named_candidates
    {op : BinaryOpOnSpectra}
    (h_named : IsNamedCandidate op)
    (h_three : ThreeConditions op) :
    op = BinaryOpOnSpectra.additive := by
  rcases h_named with hadd | hfree | hmult | hmono | hboxed
  · exact hadd
  · -- free case: rewrite hypothesis with the equation, then use the falsifier
    exfalso
    rw [hfree] at h_three
    exact freeVoiculescu_not_three_conditions h_three
  · exfalso
    rw [hmult] at h_three
    exact multFree_not_three_conditions h_three
  · exfalso
    rw [hmono] at h_three
    exact monoidalNonK_not_three_conditions h_three
  · exfalso
    rw [hboxed] at h_three
    exact boxed_at_one_not_three_conditions h_three

/-! ## Trace-channel form of the headline -/

/-- **Trace-channel corollary**: for any named candidate
satisfying ThreeConditions, the trace channel coincides with
additive convolution.  Direct consequence of v0.9.1's
`three_conditions_force_trace_law` applied to the named
candidate's underlying operation. -/
theorem named_candidate_trace_law
    {op : BinaryOpOnSpectra}
    (_h_named : IsNamedCandidate op)
    (h_three : ThreeConditions op)
    (μ ν : Spectrum) :
    Spectrum.trace (op μ ν) = Spectrum.trace (additiveConv μ ν) :=
  three_conditions_force_trace_law op h_three μ ν

/-! ## Pointwise consequence -/

/-- **Pointwise corollary of the named-candidate closure**: a named
candidate satisfying ThreeConditions equals `additiveConv`
pointwise as a multiset. -/
theorem named_candidate_pointwise_additive
    {op : BinaryOpOnSpectra}
    (h_named : IsNamedCandidate op)
    (h_three : ThreeConditions op)
    (μ ν : Spectrum) :
    op μ ν = additiveConv μ ν := by
  have h_eq : op = BinaryOpOnSpectra.additive :=
    broader_uniqueness_among_named_candidates h_named h_three
  rw [h_eq, BinaryOpOnSpectra.additive_apply]

end SpectralPhysics.CompositionBroaderUniqueness
