/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.CompositionUniqueness.MultiplicativeFails
import SpectralPhysics.CompositionUniqueness.FreeFails
import SpectralPhysics.CompositionUniqueness.AdditiveSatisfies
import SpectralPhysics.CompositionUniqueness.KasparovProductUniqueness
import SpectralPhysics.CompositionUniqueness.BroaderUniquenessOpen

/-!
# Composition Uniqueness — Honest Headline File

This file pulls together the four different scopes at which the
`CompositionUniqueness` module operates and labels each explicitly
as CLOSED, CONDITIONAL, or OPEN.

## Scope 1 (CLOSED) — restricted to named candidates

Among the three named candidate operations (`additive`,
`multiplicative`, `free`), only `additive` satisfies the three-
condition predicate.  Conditional only on the two named Minkowski-
cancellation axioms in `AdditiveSatisfies`.

## Scope 2 (CLOSED unconditionally) — trace-channel form

Any binary operation on spectra satisfying Hamiltonian additivity
agrees with additive convolution on the trace functional.  **Zero
new axioms.**

## Scope 3 (CONDITIONAL on K1+K2+K3) — Kasparov-product narrow

Within the category of Kasparov-product spectral operations
(witnessed by `KasparovProductWitness`), the three-condition
predicate is necessarily satisfied.  Uses K1 (Mesland-Rennie),
K2 (Rosenberg-Schochet), K3 (Kassel).  This corresponds to Path A
in `composition_decision.md`.

## Scope 4 (OPEN) — broader pointwise uniqueness

The claim that *any* binary operation satisfying the three
conditions equals `additiveConv` pointwise.  Recorded as the
`PointwiseUniqueness` predicate.  NOT proved.

## Contrast with the audit-caught prior version

| Aspect | Prior `compute/composition-uniqueness` | This redemption |
|---|---|---|
| Build state | `HypothesisSet.lean` + `SpectralOperations.lean` imported but never committed | both files committed; `lake build` passes |
| STATUS.md | falsely claimed "green" | honest — 4 scopes labelled |
| Broader uniqueness | "proved" via axiom-smuggled `three_conditions_force_higher_moments` (which IS the conclusion) | recorded as `PointwiseUniqueness` predicate; not proved, not axiomatised |
| Named axioms | 5 (2 axiom-smuggling) | 5 (K1/K2/K3 with literature; 2 Minkowski-cancellation, also with literature) |
| Scope discipline | claimed universal pointwise uniqueness | 3 closed scopes + 1 explicit open |
| Audit template | not applied | mirrors `compute/self-model-deficit-rigorous` |

## References

* `pre_geometric/v091_refactor/composition_decision.md` — Path A.
* `pre_geometric/lean_repo_audit/per_branch_audit.md` — audit
  that caught the prior deception.
* `compute/self-model-deficit-rigorous` — discipline template.
-/

namespace SpectralPhysics.CompositionUniqueness

/-! ## Scope 1: restricted to named candidates -/

/-- A named enumeration of the three classical candidate composition
operations on spectra. -/
inductive NamedConvolution : Type
  | additive
  | multiplicative
  | free
  deriving DecidableEq, Repr

/-- The underlying `BinaryOpOnSpectra` of a named convolution. -/
def NamedConvolution.toOp : NamedConvolution → BinaryOpOnSpectra
  | .additive       => BinaryOpOnSpectra.additive
  | .multiplicative => BinaryOpOnSpectra.multiplicative
  | .free           => BinaryOpOnSpectra.free

/-- **Scope 1 theorem (CLOSED)**: among the three named candidate
operations, *only* additive satisfies the three-condition
predicate.

Conditional on the two named Minkowski-cancellation axioms in
`AdditiveSatisfies.lean`; no other axiom is invoked. -/
theorem additive_is_unique_among_three_named
    (c : NamedConvolution) :
    ThreeConditions c.toOp ↔ c = NamedConvolution.additive := by
  constructor
  · intro h
    cases c with
    | additive       => rfl
    | multiplicative =>
        exact absurd h multiplicative_not_three_conditions
    | free           =>
        exact absurd h free_not_three_conditions
  · intro hc
    subst hc
    exact additive_satisfies_three_conditions

/-! ## Scope 2: unconditional trace-channel uniqueness -/

/-- **Scope 2 theorem (CLOSED unconditionally)**: any binary
operation on spectra satisfying the three conditions agrees with
additive convolution on the trace functional.

**Zero new axioms.**  This is the trace-level form, needed for
all downstream physics predictions (partition functions, mass
sums). -/
theorem three_conditions_force_trace_law
    (op : BinaryOpOnSpectra) (h : ThreeConditions op)
    (μ ν : Spectrum) :
    Spectrum.trace (op μ ν) = Spectrum.trace (additiveConv μ ν) :=
  trace_uniqueness_of_hamiltonian_additivity op h.hamilton μ ν

/-- **Corollary of Scope 2**: any two three-condition operations
have the same trace functional on every spectrum pair. -/
theorem three_conditions_trace_unique
    (op op' : BinaryOpOnSpectra)
    (h : ThreeConditions op) (h' : ThreeConditions op')
    (μ ν : Spectrum) :
    Spectrum.trace (op μ ν) = Spectrum.trace (op' μ ν) := by
  rw [three_conditions_force_trace_law op h μ ν,
      three_conditions_force_trace_law op' h' μ ν]

/-! ## Scope 3: Kasparov-product narrow uniqueness (re-exported) -/

/-- **Scope 3 re-export (CONDITIONAL on K1, K2, K3)**: within the
Kasparov-product spectral category, any operation carrying a
`KasparovProductWitness` satisfies the three-condition predicate.

See `KasparovProductUniqueness.lean` for the proof and the three
named axioms K1 (Mesland-Rennie), K2 (Rosenberg-Schochet),
K3 (Kassel). -/
theorem kasparov_three_conditions
    {op : BinaryOpOnSpectra} (h : KasparovProductWitness op) :
    ThreeConditions op :=
  kasparov_product_satisfies_three_conditions h

/-! ## Scope 4: broader uniqueness — HONESTLY OPEN -/

/-- **Scope 4 (OPEN)**: the v0.9 line 16783 admission, stated as a
`Prop`-valued predicate.  Not proved.  Path A declares this a
v1.0 NCG-extension target. -/
def BroaderPointwiseUniqueness : Prop := PointwiseUniqueness

/-- The conditional form: assuming the broader claim as a
hypothesis, the v0.9 admission is closed.  The hypothesis IS the
open problem; it is not discharged here. -/
theorem composition_unique_conditional_on_broader
    (h : BroaderPointwiseUniqueness)
    (op : BinaryOpOnSpectra) (htc : ThreeConditions op) :
    op = BinaryOpOnSpectra.additive :=
  composition_uniqueness_under_broader_hypothesis h op htc

end SpectralPhysics.CompositionUniqueness
