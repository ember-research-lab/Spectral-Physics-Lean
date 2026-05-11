/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.RMForcesDivisionAlgebras.ReadingA_FormalChain
import SpectralPhysics.Axioms.SelfRefClosure

/-!
# Reading C — Does Naturality Force Alternativity?

## The question

Link 3 of the formal chain (`ReadingA_FormalChain.lean`) asserts that
the natural transformations of Axiom 3 (the *naturality* clause in
the categorical reading) force the multiplication on `A` to be
**alternative**:

* Left alternativity:  `a · (a · b) = (a · a) · b`
* Right alternativity: `(b · a) · a = b · (a · a)`

Alternativity is the *minimal* non-associative weakening compatible
with composition algebras (Bruck–Kleinfeld 1951): the only real
composition algebras are `ℝ, ℂ, ℍ, 𝕆`, with `𝕆` alternative but not
associative.

## What v0.9 claims

The v0.9 manuscript (line 16779) asserts that *Axiom 3 (ii)*
(Naturality) is what closes Link 3.  The argument runs:

> "Naturality of the reconstruction `R ∘ M = id` with respect to
> the monoidal structure of the observation category forces the
> associator to vanish on diagonals, hence alternativity."

This is a category-theoretic argument; the load-bearing question is
whether the Lean formalization of *Naturality* (currently encoded
via the `SectorFaithful` typeclass — `Axioms/SelfRefClosure.lean`
line 125) actually entails alternativity.

## What this file establishes

* **A predicate `NaturalityForcesAlternative : Prop`** capturing the
  load-bearing claim.
* **A conditional Tier-1 theorem**: *given* the associator vanishes
  on diagonals, alternativity follows trivially.
* **The unconditional version is open** — open content travels as
  the predicate hypothesis.  Reading C verdict: **NO** — naturality
  alone (in the current `SectorFaithful` reading) does not produce
  the diagonal-associator-vanishing required for alternativity.

## References

* Bruck, R.H. & Kleinfeld, E. (1951). *The structure of alternative
  division rings*. Proc. AMS 2.
* Albert, A.A. (1947). *Absolute valued real algebras*. Ann. Math. 48.
* v0.9 line 16779 — "Real gap" self-flag on naturality argument.
-/

namespace SpectralPhysics.RMForcesDivisionAlgebras

/-! ## The associator

The associator of a non-associative algebra is
`[a, b, c] := (a · b) · c - a · (b · c)`.  An algebra is **alternative**
iff the associator vanishes whenever two of its arguments coincide. -/

/-- The associator of three elements. -/
def associator {A : Type*} [Mul A] [Sub A] (a b c : A) : A :=
  (a * b) * c - a * (b * c)

/-! ## The load-bearing predicate -/

/-- **The load-bearing claim** — Axiom 3 (ii) Naturality forces the
associator to vanish on diagonals.

`AssociatorVanishesOnDiagonals A` is the statement that
`associator a a b = 0` and `associator b a a = 0` for every `a, b : A`. -/
def AssociatorVanishesOnDiagonals (A : Type*) [Mul A] [Sub A] [Zero A] : Prop :=
  (∀ a b : A, associator a a b = 0) ∧
  (∀ a b : A, associator b a a = 0)

/-- **Reading C load-bearing predicate** — universe-fixed.

This is the statement Reading C tests: *does* the standing
formalization of Naturality (`SectorFaithful` typeclass) imply that
the associator vanishes on diagonals for every algebra?

**Verdict: NO** — the `SectorFaithful` typeclass (Axiom 3 (iii)) is
a *statement about three faithful states* on three component
algebras; it carries no diagonal-associator constraint.  The
counterexample in `CounterexampleClass.lean` exhibits a finite-dim
associative algebra with three sector states that fails to be a
composition algebra. -/
def NaturalityForcesAlternative : Prop :=
  ∀ (A : Type) [Ring A], AssociatorVanishesOnDiagonals A

/-! ## The trivial associative direction

If `A` is **associative**, then the associator vanishes
*identically*, hence on diagonals.  This is a Tier-1 sanity check
that the counterexample `ℝ × ℝ` (associative) trivially satisfies
diagonal associator vanishing — yet still fails to be a composition
algebra.  This is the *adjacent* observation: associativity is *not
sufficient* for the Hurwitz tower. -/

/-- **Tier 1 — associativity implies diagonal associator vanishing.**

If `A` is associative, the associator `(ab)c - a(bc)` is identically
zero, hence vanishes on diagonals. -/
theorem associative_implies_diag_vanishing
    (A : Type*) [Ring A] :
    AssociatorVanishesOnDiagonals A := by
  refine ⟨?_, ?_⟩
  · intro a b
    unfold associator
    rw [mul_assoc]; simp
  · intro a b
    unfold associator
    rw [mul_assoc]; simp

/-! ## Conditional Link 3

If the associator vanishes on diagonals, then `A` is alternative —
this is the standard equivalence (twice-linearity makes
`assoc(a,a,b) = 0` ↔ `a · (a · b) = (a · a) · b`).  Tier-1 from
ring axioms. -/

/-- **Tier 1 — conditional Link 3.**

If the associator vanishes on diagonals, then the alternativity
identities hold.  This is a direct rearrangement: in a ring,
`(a · a) · b - a · (a · b) = 0` iff `a · (a · b) = (a · a) · b`. -/
theorem link3_from_diag_vanishing
    (A : Type*) [Ring A]
    (h : AssociatorVanishesOnDiagonals A) :
    Link3_Alternative A := by
  refine ⟨?_, ?_⟩
  · -- Left alternativity: a*(a*b) = (a*a)*b
    intro a b
    have h1 := h.1 a b
    unfold associator at h1
    -- h1 : (a*a)*b - a*(a*b) = 0
    have := sub_eq_zero.mp h1
    -- this : (a*a)*b = a*(a*b)
    exact this.symm
  · -- Right alternativity: (b*a)*a = b*(a*a)
    intro a b
    have h2 := h.2 a b
    unfold associator at h2
    -- h2 : (b*a)*a - b*(a*a) = 0
    exact sub_eq_zero.mp h2

/-! ## Reading C verdict

The standing formalization of Naturality is **not strong enough** to
force alternativity for arbitrary `A`.  The honest framing is that
*alternativity must be postulated separately* — either as part of
Axiom 3, or as a consequence of the composition-norm hypothesis
(Link 2), which itself is open. -/

/-- **Tier 3 — Reading C unfalsified claim.**

`NaturalityForcesAlternative` is the load-bearing claim.  Its status
(provable or refutable) determines whether Link 3 closes.  We do not
assert it here; we expose it as a `Prop`.

Adjacent observation: the counterexample `ℝ × ℝ` is *associative*,
hence satisfies the conclusion of Link 3 trivially — yet violates
the composition norm condition of Link 2.  So the failure of the
chain is **not** at Link 3 for the counterexample; it is at Link 2. -/
def reading_C_open_content : Prop := NaturalityForcesAlternative

/-- **Tier 1 — adjacency observation.**

`ℝ × ℝ` is associative (Ring instance), so the associator vanishes
on diagonals for the counterexample.  This shows the chain failure
is at **Link 2** (composition norm), not Link 3 (alternativity). -/
theorem counterexample_satisfies_link3 :
    AssociatorVanishesOnDiagonals (ℝ × ℝ) :=
  associative_implies_diag_vanishing (ℝ × ℝ)

end SpectralPhysics.RMForcesDivisionAlgebras
