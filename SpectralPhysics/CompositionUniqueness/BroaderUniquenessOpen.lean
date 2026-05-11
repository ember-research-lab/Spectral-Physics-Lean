/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.CompositionUniqueness.HypothesisSet
import SpectralPhysics.CompositionUniqueness.AdditiveSatisfies

/-!
# Broader Composition Uniqueness — HONESTLY OPEN

This file records, as **predicate hypotheses** (NOT as theorems
and NOT as axioms), the broader uniqueness claim that v0.9 line
16783 originally hand-waved at:

> "additive convolution is the unique operation that factors
> spectra in a way compatible with faithfulness of both factors."

Stated honestly: this asserts that *any* binary operation on
`Spectrum` satisfying the spectrum-level three-condition predicate
must equal `additiveConv` pointwise as a multiset.  This is the
v1.0 NCG-extension target identified in
`pre_geometric/v091_refactor/composition_decision.md`.

## Why predicates, not theorems or axioms

The audit-discipline established in
`compute/self-model-deficit-rigorous` says: when a claim is
genuinely open and the path to closing it requires infrastructure
not yet in Mathlib, the honest move is to record the claim as a
**Prop-valued predicate** that downstream callers may assume as a
hypothesis, NOT as a theorem (which would be `sorry` or
axiom-smuggled) and NOT as an axiom (which would pretend the claim
is a settled external result rather than the open question we are
flagging).

## The (open) predicates

* `BroaderUniqueness op` — *if* `op` satisfies the three
  conditions, *then* it agrees with additive convolution.
* `PointwiseUniqueness` — universally-quantified version (any
  three-condition operation equals additive convolution).

These are stated.  They are NOT proved here.

## What IS proved here

* `trace_uniqueness_of_hamiltonian_additivity` — unconditional
  trace-level uniqueness for *any* operation satisfying
  Hamiltonian additivity.  This is the only unconditional result
  in this file.
* `additive_satisfies_broader_uniqueness` — additive convolution
  satisfies `BroaderUniqueness` (trivially, by reflexivity).
  Carries no content; sanity check on the predicate.
* `composition_uniqueness_under_broader_hypothesis` — the
  conditional form: assuming `PointwiseUniqueness` as a
  hypothesis, the v0.9 line 16783 admission is closed.

## What is NOT proved here

* `PointwiseUniqueness` itself.  This is the actual v0.9 line
  16783 hand-wavy admission.  Path A declares it a v1.0
  NCG-extension target.

## References

* v0.9 line 16783 (the hand-wavy admission).
* `pre_geometric/v091_refactor/composition_decision.md` Path A.
* `compute/self-model-deficit-rigorous` STATUS.md (the discipline
  template).
-/

namespace SpectralPhysics.CompositionUniqueness

/-! ## The open predicates -/

/-- **The broader-uniqueness predicate (open)**: *if* the operation
`op` satisfies the three-condition bundle, *then* it agrees with
additive convolution on every input pair.

This is the implication form of the v0.9 line 16783 admission.
It is NOT a theorem proved in this file; it is a *predicate*
that downstream callers may assume as a hypothesis. -/
def BroaderUniqueness (op : BinaryOpOnSpectra) : Prop :=
  ThreeConditions op →
    ∀ μ ν : Spectrum, op μ ν = additiveConv μ ν

/-- **The universally-quantified broader-uniqueness predicate (open)**.
Any three-condition operation equals additive convolution pointwise.

This is the headline open problem of the `CompositionUniqueness`
module: the v0.9 line 16783 admission, stated honestly as a `Prop`
that has not been proved here.

Path A (per `composition_decision.md`) declares this a v1.0
NCG-extension target. -/
def PointwiseUniqueness : Prop :=
  ∀ op : BinaryOpOnSpectra,
    ThreeConditions op → op = BinaryOpOnSpectra.additive

/-! ## What we can say without proving `PointwiseUniqueness` -/

/-- `additive` trivially satisfies `BroaderUniqueness`
(`additiveConv μ ν = additiveConv μ ν`).  Sanity check on the
predicate; carries no content. -/
theorem additive_satisfies_broader_uniqueness :
    BroaderUniqueness BinaryOpOnSpectra.additive := by
  intro _ μ ν
  rw [BinaryOpOnSpectra.additive_apply]

/-- **Conditional implication**: assuming `PointwiseUniqueness` as
a hypothesis, the v0.9 line 16783 admission is closed.

Any caller using this theorem MUST supply the hypothesis — there
is no path within this branch to discharge it. -/
theorem composition_uniqueness_under_broader_hypothesis
    (h : PointwiseUniqueness)
    (op : BinaryOpOnSpectra) (htc : ThreeConditions op) :
    op = BinaryOpOnSpectra.additive :=
  h op htc

/-! ## Trace-channel form is unconditional -/

/-- Any binary operation on spectra satisfying Hamiltonian
additivity produces the same trace as additive convolution.

This is the *unconditional* trace-level form of the
composition-uniqueness claim.  Holds for **every** binary
operation in `BinaryOpOnSpectra` that satisfies the
Hamiltonian-additivity predicate; no other hypothesis, axiom, or
witness is needed. -/
theorem trace_uniqueness_of_hamiltonian_additivity
    (op : BinaryOpOnSpectra) (h : HamiltonianAdditivity op)
    (μ ν : Spectrum) :
    Spectrum.trace (op μ ν) = Spectrum.trace (additiveConv μ ν) := by
  rw [h μ ν, trace_additiveConv]

end SpectralPhysics.CompositionUniqueness
