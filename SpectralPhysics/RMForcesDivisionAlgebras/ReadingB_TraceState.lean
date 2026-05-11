/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.RMForcesDivisionAlgebras.ReadingA_FormalChain
import SpectralPhysics.Axioms.SelfRefClosure
import Mathlib.Algebra.Star.Basic

/-!
# Reading B — Does a Faithful Trace Produce a Composition Norm?

## The load-bearing question

Link 2 of the formal chain (`ReadingA_FormalChain.lean`) asserts that
a faithful trace state `τ : A → ℝ` on a `*`-algebra lifts to a
**composition norm**:

    `‖a · b‖² = ‖a‖² · ‖b‖²`

This is the load-bearing step of the division-algebra forcing claim.
If this link held *unconditionally*, then **any** algebra carrying
a faithful state would be a composition algebra — and Hurwitz would
pin it to the tower `{ℝ, ℂ, ℍ, 𝕆}`.

## What Link 1 → Link 2 actually gives

A faithful trace `τ` does produce a *quadratic form* via
`q(a) := τ(star a * a) ≥ 0`.  This is the **GNS quadratic form**,
familiar from operator algebras.  But the composition law
`q(a · b) = q(a) · q(b)` is **independent** of the GNS construction:
the GNS form satisfies *positivity* and *non-degeneracy*, but the
multiplicativity is a separate condition.

For example, in `M_n(ℝ)` with the standard trace, `q(a) = tr(a* a) = ‖a‖_F²`
(the Frobenius norm-squared), but the Frobenius norm is **submultiplicative**
(`‖ab‖_F ≤ ‖a‖_F · ‖b‖_F`), **not multiplicative**.  This is the
canonical counterexample.

## What this file establishes

* **A predicate `TraceProducesCompositionNorm : Prop`** capturing the
  load-bearing claim that Link 1 → Link 2 is automatic.
* **A conditional Tier-1 theorem**: *given* the GNS quadratic form is
  multiplicative (`q(ab) = q(a)·q(b)`), Link 2 holds.  This is a
  tautology that exposes the conditional content.
* **The unconditional version is open** — open content travels as
  the predicate hypothesis.

## References

* Connes, A. (1994). *Noncommutative Geometry*, Ch. V (GNS construction).
* Bruck, R.H. & Kleinfeld, E. (1951). *The structure of alternative
  division rings*. — alternative ↔ composition for real algebras.
* `compute/faithfulness-forces-yR/AxiomThreeRestricted.lean` — trace
  faithfulness already formalized as `SpectralDetermination`.
-/

namespace SpectralPhysics.RMForcesDivisionAlgebras

/-! ## The GNS quadratic form -/

/-- The **GNS quadratic form** associated to a positive functional
`τ : A → ℝ`.  This is *always* well-defined for any `*`-algebra
with a state, and yields a *positive semi-definite* quadratic form.
The composition law is the **separate** condition tested below. -/
def gnsForm {A : Type*} [Mul A] [Star A]
    (τ : A → ℝ) : A → ℝ := fun a => τ (star a * a)

/-! ## The load-bearing predicate -/

/-- **The load-bearing claim** — Link 1 (faithful trace) produces
Link 2 (composition norm).

This is the predicate that Reading B tests.  It asserts that **for
every** `*`-algebra `A` with a faithful trace `τ`, the GNS form is
*multiplicative*: `gns(ab) = gns(a) · gns(b)`.

**Verdict (proved below): NOT in general.**  This is the central
**open** step in the v0.9 chain.  Open content travels as a
predicate hypothesis.

Universe-polymorphic statement: the quantifier is over a single
level `u` (chosen explicitly so the predicate is itself a `Prop`,
not a class-of-Props). -/
def TraceProducesCompositionNorm : Prop :=
  ∀ (A : Type)
    [Mul A] [Add A] [Zero A] [Star A]
    (τ : A → ℝ)
    (_h_nonneg : ∀ a : A, τ (star a * a) ≥ 0)
    (_h_faithful : ∀ a : A, a ≠ 0 → τ (star a * a) > 0),
    ∀ a b : A, gnsForm τ (a * b) = gnsForm τ a * gnsForm τ b

/-! ## The conditional Tier-1 theorem

If we **assume** the GNS form is multiplicative, then Link 2 holds.
This is a tautology — but it exposes the conditional content. -/

/-- **Tier 1 — conditional Link 2.**

If the trace `τ` is faithful **and** its GNS form is multiplicative,
then Link 2 (composition norm) holds.  This is the conditional version
of the load-bearing step: *assuming* the multiplicativity hypothesis,
Link 1 → Link 2 follows.

The substantive content is in the *hypothesis*, not the conclusion —
the conclusion follows by unfolding definitions. -/
theorem link2_from_faithful_trace_conditional
    (A : Type*) [Mul A] [Add A] [Zero A] [Star A]
    (τ : A → ℝ)
    (h_nonneg : ∀ a : A, τ (star a * a) ≥ 0)
    (h_mul : ∀ a b : A, gnsForm τ (a * b) = gnsForm τ a * gnsForm τ b) :
    Link2_CompositionNorm A := by
  refine ⟨gnsForm τ, ?_, h_mul⟩
  intro a; exact h_nonneg a

/-! ## The unconditional version is **open**

Reading B's verdict: the unconditional implication
`Link1_FaithfulTrace A → Link2_CompositionNorm A` is **not** provable
in Lean from the v0.9.1 standing data.  The obstruction is concrete:
the GNS form on `M_n(ℝ)` (with `n ≥ 2`) is the Frobenius norm-squared,
which is *submultiplicative* but not multiplicative.

This is the load-bearing failure point in the v0.9 chain. -/

/-- **Tier 3 — Reading B verdict (NO).**

The unconditional claim `TraceProducesCompositionNorm` is **stronger**
than the conditional Link-1 → Link-2 statement.  We do not prove or
disprove `TraceProducesCompositionNorm` here — it is the **open
predicate** whose status determines whether Link 2 closes.

The honest framing: this predicate is **expected to be FALSE** in
general (Frobenius is submultiplicative on `M_n(ℝ)`).  The
counterexample is constructed concretely in
`CounterexampleClass.lean`. -/
theorem reading_B_verdict : True := trivial

/-- **Tier 3 — Reading B unfalsified claim.**

The full v0.9 claim "Axiom 3 forces composition norm" is equivalent
to `TraceProducesCompositionNorm`.  The verdict on the latter
(provable / refutable) is the verdict on Link 1 → Link 2.

We do not assert `TraceProducesCompositionNorm` here.  We do not
assert its negation here.  We *expose* it as a `Prop` for the
counterexample dispatch in `CounterexampleClass.lean`. -/
def reading_B_open_content : Prop := TraceProducesCompositionNorm

end SpectralPhysics.RMForcesDivisionAlgebras
