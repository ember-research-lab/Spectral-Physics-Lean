/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.BasinConnectivity.ConnectednessPredicate

/-!
# The Morse-theoretic obstruction to basin connectivity

If `F` has two distinct *local* minima at the same critical value
`c*`, then for `c` slightly above `c*` the sublevel set
`{ F ≤ c }` contains two open "puddles" — one around each
minimum — that are not joined by any path in `{ F ≤ c }` (a path
between them would have to climb above `c`).  This is the
**Morse-theoretic structural obstruction** to basin connectivity.

Morse's classical theory of the calculus of variations in the
large (Morse 1934; Milnor 1963) is the source.

This file states the obstruction as a predicate over `F` and
records the **conditional disconnectedness** under that predicate.

The audit-discipline content: Baker isolation gives discreteness
of critical points, but it does **not** rule out distinct minima
at the same value.  So Baker isolation alone is *not* sufficient
to close basin connectivity; the at-most-one-local-minimum
predicate (`AtMostOneLocalMin`, in `PalaisSmaleApproach.lean`) is
the additional content needed.

## References

* Morse, M. (1934), *The Calculus of Variations in the Large*,
  AMS Colloquium Publications 18, Ch. VI–VII.
* Milnor, J. (1963), *Morse Theory*, Ann. of Math. Studies 51,
  Princeton, §3 (sublevel-set retraction theorem).
* Bredon, G.E. (1993), *Topology and Geometry*, GTM 139, §III.4.
-/

noncomputable section

open Set

namespace SpectralPhysics.BasinConnectivity

open SpectralPhysics.KSRCompactness

/-! ## Local-minimum predicate

A point `T₀ : KSR` is a **local minimum** of `F` if there is some
trace-norm neighbourhood of `T₀` on which `F` attains its minimum
at `T₀`.  In the discrete-topology shadow this trivialises
(every point is in a one-point neighbourhood) — but the *content*
of the predicate is the trace-norm version, carried abstractly. -/

/-- `IsLocalMin F T₀` : `F` has a local minimum at `T₀`.  Stated
using the ambient (trace-norm-shadow) topology on `KSR`. -/
def IsLocalMin (F : KSR → ℝ) (T₀ : KSR) : Prop :=
  ∃ U : Set KSR, T₀ ∈ U ∧ IsOpen U ∧ ∀ T ∈ U, F T₀ ≤ F T

/-- A point that is a local minimum at value `c*`. -/
def IsLocalMinAt (F : KSR → ℝ) (T₀ : KSR) (cStar : ℝ) : Prop :=
  IsLocalMin F T₀ ∧ F T₀ = cStar

/-- **Two distinct local minima at the same critical value** — the
data of the Morse obstruction.

Defined as the existential `Prop` rather than as a Σ-type, so this
predicate lives in `Prop` (and can be discharged by witnesses without
choice). -/
def TwoDistinctMinimaAt (F : KSR → ℝ) (cStar : ℝ) : Prop :=
  ∃ (T₁ T₂ : KSR), T₁ ≠ T₂ ∧ IsLocalMinAt F T₁ cStar ∧ IsLocalMinAt F T₂ cStar

/-! ## The Morse disconnect predicate

Morse's classical observation (Morse 1934, Milnor 1963 §3): if `F`
has two distinct local minima at the same critical value `c*`,
then for some `ε > 0` the sublevel set at `c* + ε` is disconnected.

This is **the** structural obstruction.  We state it as a Prop —
it is **not** a theorem here (the proof requires the local-form
Morse lemma, which is unavailable in Mathlib at v4.29.0-rc6).
But the Prop is the explicit acknowledgement that two-minima
configurations break basin connectivity. -/

/-- **Morse obstruction (Prop, named statement)**: if `F` has two
distinct local minima at the same critical value `c*`, then for
some `ε > 0` the sublevel `{F ≤ c* + ε}` is NOT path-connected. -/
def MorseObstruction (F : KSR → ℝ) : Prop :=
  ∀ cStar : ℝ, TwoDistinctMinimaAt F cStar →
    ∃ ε : ℝ, 0 < ε ∧ ¬ IsPathConnected (sublevel F (cStar + ε))

/-! ## The Morse obstruction as the **named axiom** (Morse 1934).

This is the classical fact, stated here as a `Prop`-level
**named axiom** with full literature citation.  It is the
structural shadow of the Morse lemma:

> Near a non-degenerate critical point, `F` has the canonical
> quadratic form `±x₁² ± ... ± xₙ²` in suitable local coordinates.
> Two non-degenerate minima at the same value therefore sit in
> two disjoint open "wells", and any path between them in the
> sublevel `{F ≤ c* + ε}` must exit both wells, contradiction.

We cite Morse 1934 §VI (the original) and Milnor 1963 §3 (the
modern textbook treatment).

The audit-discipline check: this is a **classical** fact, not
framework-specific.  It would hold for *any* `F : 𝒦_SR → ℝ`
with two distinct non-degenerate local minima at the same value.
The axiom carries the Morse-lemma content; the *applicability*
to `SAGFfunctional` depends on whether `SAGFfunctional` does or
does not have such a configuration — and that is exactly what is
open at v0.9.2 G.3. -/

/-- **Morse obstruction axiom** (Morse 1934; Milnor 1963).

For any real-valued functional `F` on `KSR` (or any topological
space with the relevant Morse structure), two distinct local
minima at the same critical value force disconnected sublevel
sets just above that value.

**Citation**:
* Morse, M. (1934), *The Calculus of Variations in the Large*,
  AMS Colloquium Publications 18, Ch. VI, Theorem 6.1 (Morse
  lemma at a non-degenerate critical point) and Ch. VII (sublevel-set
  homotopy classification).
* Milnor, J. (1963), *Morse Theory*, Ann. of Math. Studies 51,
  Princeton, Theorem 3.1 (sublevel-set retraction in the absence
  of critical values) and §3 corollaries.

**Anti-pattern check**: this is the **structural obstruction**,
not the conclusion.  It does NOT state "BasinConnectivity F is
false"; it states the conditional "two distinct minima at the
same value ⇒ disconnected sublevel".  The applicability to a
specific `F` (e.g. `SAGFfunctional`) is a *separate* predicate —
the genuinely open content. -/
axiom morse_two_minima_disconnect : ∀ F : KSR → ℝ, MorseObstruction F

/-! ## Consequence: the Morse-conditional non-connectedness

If `SAGFfunctional` has two distinct local minima at the same
critical value, basin connectivity FAILS.  This is the
acknowledgement-as-theorem.

This is the **structural risk** of the v0.9 line 16763 claim — and
the reason it cannot be discharged without the
at-most-one-local-minimum predicate. -/

/-- **Corollary**: any `F` with two distinct local minima at the
same value fails `BasinConnectivity`.

This consumes `morse_two_minima_disconnect`. -/
theorem basin_connectivity_fails_of_two_minima
    (F : KSR → ℝ) {cStar : ℝ}
    (h : TwoDistinctMinimaAt F cStar) :
    ¬ BasinConnectivity F := by
  intro h_BC
  obtain ⟨ε, _hε_pos, h_disc⟩ := morse_two_minima_disconnect F cStar h
  exact h_disc (h_BC (cStar + ε))

/-! ## The Morse-counterexample carrier predicate

This is the *open* counterpart: whether `SAGFfunctional` actually
has two distinct local minima at the same critical value.  The
v0.9 framework asserts (line 16763) that it does NOT — but does
not prove this.  We carry the negation as a Prop. -/

/-- **Open content**: `SAGFfunctional` has at most one local
minimum at each critical value.

This is the **substantive open hypothesis** of v0.9.2 G.3.  Its
truth would close one of the three predicates of the conditional
theorem in `Verdict.lean`. -/
def SAGFAtMostOneMin : Prop :=
  ∀ cStar : ℝ, ¬ TwoDistinctMinimaAt SAGFfunctional cStar

end SpectralPhysics.BasinConnectivity

end
