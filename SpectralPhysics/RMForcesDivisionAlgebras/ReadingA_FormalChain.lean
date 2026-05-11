/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Axioms.SelfRefClosure
import SpectralPhysics.Algebra.Hurwitz
import SpectralPhysics.Algebra.Forcing
import Mathlib.Algebra.Algebra.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Reading A — The Formal 4-Link Chain

## v0.9.2 deferred item G.4

v0.9 line 16779 self-flags as **"Real gap"** the claim that
Axiom 3 (Reconstruction `R ∘ M = id` + Naturality) forces the
observation algebra to be a normed division algebra — i.e. one of
the Hurwitz tower `{ℝ, ℂ, ℍ, 𝕆}`.

This file states the v0.9 claim as a **four-link chain** of named
predicates, marks which links are Tier-1-closable here and which
remain conditional, and prepares the conditional implication
`(all four links) → Hurwitz tower` for use in the counterexample
falsification in `CounterexampleClass.lean` and the headline verdict
in `Verdict.lean`.

## The four links

* **Link 1.** Axiom 3 (i) Reconstruction `R ∘ M = id` + (ii) Naturality
  produce a faithful trace state on the algebra.
* **Link 2.** A faithful trace state lifts to a norm satisfying the
  *composition law* `‖ab‖ = ‖a‖·‖b‖`.
* **Link 3.** A composition norm forces the algebra to be
  *alternative* and *power-associative*.
* **Link 4.** A real alternative composition algebra lies in the
  Hurwitz tower (Hurwitz 1898).

Links 1, 3 are **Tier 3 / conditional** in this file: they travel as
named predicate hypotheses. Link 4 is the already-axiomatized
`hurwitz_dim` / `composition_dim_le_eight_axiom` from
`SpectralPhysics/Algebra/Hurwitz.lean` (Hurwitz 1898, Albert 1947,
Bruck–Kleinfeld 1951). Link 2 is the **load-bearing** middle step
tested in `ReadingB_TraceState.lean`.

## References

* Hurwitz, A. (1898/1923). "Über die Composition der quadratischen Formen."
* Albert, A.A. (1947). "Absolute valued real algebras." Ann. Math. 48.
* Bruck, R.H. & Kleinfeld, E. (1951). "The structure of alternative
  division rings." Proc. AMS 2.
* v0.9 line 16779 — author's own "Real gap" self-flag.
* `compute/faithfulness-forces-yR` — adjacent negative on `y_R`.
-/

namespace SpectralPhysics.RMForcesDivisionAlgebras

/-! ## Algebraic carrier

We work with a finite-dimensional unital ℝ-algebra `A`. The full
v0.9 claim is conditional on `A` being the observation algebra in
the sense of `SpectralPhysics/Algebra/Forcing.lean`. Here we ask
whether Axiom 3 alone forces the Hurwitz tower **without** the
`CompositionAlgebra` instance already being supplied.

The strategy: instead of building a class that bundles every
required hypothesis (which begs the question), we travel each link
as a `Prop` predicate. The conditional chain is then an honest
implication, and the falsification in `CounterexampleClass.lean`
exhibits an `A` that satisfies the **starting** predicates but
not the **target** predicate. -/

/-- **Link 1 predicate** — Axiom 3 produces a faithful trace.

In the v0.9 formal chain, Axiom 3 (i) Reconstruction + (ii) Naturality
should yield a faithful trace state `τ : A → ℝ`.  We state this as a
hypothesis: existence of a positive faithful linear functional. -/
def Link1_FaithfulTrace (A : Type*) [Mul A] [Add A] [Zero A] [Star A] : Prop :=
  ∃ τ : A → ℝ,
    (∀ a : A, τ (star a * a) ≥ 0) ∧
    (∀ a : A, a ≠ 0 → τ (star a * a) > 0)

/-- **Link 2 predicate** — a faithful trace lifts to a composition
norm `‖ab‖ = ‖a‖·‖b‖`.

This is the load-bearing link.  In `ReadingB_TraceState.lean` we
test whether Link 1 → Link 2 is closable; the verdict there is
**conditional** — the trace gives only a *quadratic form*, and the
multiplicativity `‖ab‖² = ‖a‖²·‖b‖²` is an *additional* hypothesis
not produced by Axiom 3 alone. -/
def Link2_CompositionNorm (A : Type*) [Mul A] : Prop :=
  ∃ n : A → ℝ,
    (∀ a : A, n a ≥ 0) ∧
    (∀ a b : A, n (a * b) = n a * n b)

/-- **Link 3 predicate** — a composition norm forces *alternative*
multiplication.

Alternativity: `a · (a · b) = (a · a) · b` and `(b · a) · a = b · (a · a)`.
Hurwitz's theorem requires alternativity to pin the tower at
`{ℝ, ℂ, ℍ, 𝕆}`.  Composition algebras are alternative
(Bruck–Kleinfeld 1951). -/
def Link3_Alternative (A : Type*) [Mul A] : Prop :=
  (∀ a b : A, a * (a * b) = (a * a) * b) ∧
  (∀ a b : A, (b * a) * a = b * (a * a))

/-- **Link 4 predicate** — alternative composition algebra lies in
the Hurwitz tower `{1, 2, 4, 8}`.

This is the already-axiomatized content of `Hurwitz.lean`: every
finite-dim real composition algebra has dimension in `{1, 2, 4, 8}`. -/
def Link4_HurwitzTower (A : Type*) [AddCommGroup A] [Module ℝ A]
    [FiniteDimensional ℝ A] : Prop :=
  Module.finrank ℝ A ∈ ({1, 2, 4, 8} : Set ℕ)

/-! ## The conditional chain

We now state the chain `Link 1 ∧ Link 2 ∧ Link 3 → Link 4`.  Each
implication is **either** a named lemma here (Tier 1) **or** a
predicate hypothesis (Tier 3).  -/

/-- **The full chain as a single proposition.**

`R ∘ M = id + Naturality → Hurwitz tower` is the v0.9 claim.  In
this file we package it as the conjunction of the four links. -/
def FullChain (A : Type*)
    [Ring A] [Star A] [Module ℝ A] [FiniteDimensional ℝ A] : Prop :=
  Link1_FaithfulTrace A ∧
  Link2_CompositionNorm A ∧
  Link3_Alternative A ∧
  Link4_HurwitzTower A

/-! ## Tier classification

### Tier 1 (closable here)

* **Link 4** is the existing `composition_dim_le_eight_axiom` /
  `hurwitz_dim` from `Hurwitz.lean`.  We expose it as a Tier 1
  named theorem (`link4_via_hurwitz`).

### Tier 3 (open / conditional)

* **Link 1** is conditional on Axiom 3 reading; the
  `compute/faithfulness-forces-yR` session shows that *all five
  standing readings* of Axiom 3 do **not** uniquely select a
  faithful trace — they admit a continuum.
* **Link 2** is the **load-bearing** open link.  Tested
  conditionally in `ReadingB_TraceState.lean`.
* **Link 3** is conditional on the algebra being a composition
  algebra; tested separately in `ReadingC_NaturalityForcesAlt.lean`.

## Why the chain does **not** close

`CounterexampleClass.lean` exhibits an explicit algebra `A = ℝ × ℝ`
that **satisfies Link 1** (a faithful trace exists) and is
**finite-dim associative**, but **fails Link 2** (no composition
norm exists, because it has zero divisors) and **violates Link 4**
(`finrank ℝ (ℝ × ℝ) = 2`, but `ℝ × ℝ ≄ ℂ` — it is not in the tower).

This is the v0.9.2 honest finding: **Axiom 3 alone cannot bridge
Links 1 and 2**.  An additional structural hypothesis is required —
either composition-multiplicativity is *postulated* as part of
Axiom 3, or *some other* mechanism (e.g. Riesz representation,
positivity of all observables, a unitarity-from-reconstruction
argument) is required.
-/

/-- **Tier 1 — Link 4 via Hurwitz.**

A finite-dim composition algebra over ℝ has dimension in
`{1, 2, 4, 8}`.  Direct from `Hurwitz.composition_dim_le_eight_axiom`
plus `composition_dim_power_of_two`. -/
theorem link4_via_hurwitz
    (A : Type*) [NormedRing A] [InnerProductSpace ℝ A]
    [CompositionAlgebra A] [FiniteDimensional ℝ A] [Nontrivial A] :
    Link4_HurwitzTower A := by
  unfold Link4_HurwitzTower
  exact hurwitz_dim A

/-- **The conditional chain as a Tier-3 implication.**

Under the **predicate hypotheses** that Links 1–3 hold, plus a
`CompositionAlgebra` instance bridging Links 2–3 to the Hurwitz
infrastructure, Link 4 follows.

This is an **honest conditional**: the antecedents Link 1, Link 2,
Link 3 are themselves Tier-3 in our setting, and the implication
arrow does *not* discharge them.  In particular, the
`CompositionAlgebra A` instance is an *additional* hypothesis not
produced by Axiom 3 alone.  -/
theorem chain_conditional
    (A : Type*) [NormedRing A] [InnerProductSpace ℝ A] [Star A]
    [CompositionAlgebra A] [FiniteDimensional ℝ A] [Nontrivial A]
    (_h1 : Link1_FaithfulTrace A)
    (_h2 : Link2_CompositionNorm A)
    (_h3 : Link3_Alternative A) :
    Link4_HurwitzTower A :=
  link4_via_hurwitz A

/-! ## Honest accounting

* Link 1 — *trace-state existence*: **Tier 3 / conditional**.
  Open content travels as `Link1_FaithfulTrace A`.
* Link 2 — *trace → composition norm*: **Tier 3 / conditional**.
  Open content travels as `Link2_CompositionNorm A`.  This is the
  load-bearing failure point (see `ReadingB_TraceState.lean`).
* Link 3 — *composition → alternative*: **Tier 3 / conditional**.
  Open content travels as `Link3_Alternative A` (see
  `ReadingC_NaturalityForcesAlt.lean`).
* Link 4 — *Hurwitz tower*: **Tier 1** via the existing
  `composition_dim_le_eight_axiom` named axiom in `Hurwitz.lean`,
  citing Hurwitz (1898). -/

end SpectralPhysics.RMForcesDivisionAlgebras
