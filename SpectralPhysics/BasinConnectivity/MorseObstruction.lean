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

variable [TopologicalSpace KSR]

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

**2026-08-18 content audit (U6) correction.** The axiom below does NOT
carry the Morse-lemma content described here. Under the placeholder
**discrete** topology on `KSR` its conclusion is automatic (any two-point
set fails `IsPathConnected`), so `morse_two_minima_disconnect` is SHELL —
provable outright, importing nothing from Morse 1934 / Milnor 1963. The
*applicability* to `SAGFfunctional` remains open at v0.9.2 G.3, but this
file contributes no Morse content toward it. -/

/-! **2026-09-10 soundness census — axiom DELETED (UNSOUND, compile-verified).**
The U1 fix (fb15e7f, 2026-09-07) removed the discrete placeholder and put
`variable [TopologicalSpace KSR]` above, which silently made the former
`axiom morse_two_minima_disconnect : ∀ F, MorseObstruction F` quantify over
EVERY topology on `KSR`. Under the indiscrete topology `⊤` with `F ≡ 0` it
derives `False` (hostile `H01_MorseFalse.lean`, census artifact
`~/ember-review/artifacts-2026-09-10/lean-soundness-census/`). The honest
negative is now proved below as `morse_obstruction_not_universal`, and
`MorseObstruction F` is a **named hypothesis** at every use site, matching
the U1 (compactness) and U7 (three generations) repairs.

**Citation for the intended content (not formalized here)**:
* Morse, M. (1934), *The Calculus of Variations in the Large*,
  AMS Colloquium Publications 18, Ch. VI, Theorem 6.1 and Ch. VII.
* Milnor, J. (1963), *Morse Theory*, Ann. of Math. Studies 51, Theorem 3.1
  and §3 corollaries. The Morse lemma needs a smooth structure and
  non-degenerate minima; `MorseObstruction` assumes neither, so it cannot hold
  for arbitrary `F` and topology. -/

/-- Second point of `KSR`, distinct from `KSR.zero` (used by the honest negative). -/
private def ksrOther : KSR := { lam := fun _ => 0, trace_class := by simp, srInvariant := False }

private theorem zero_ne_ksrOther : KSR.zero ≠ ksrOther := by
  intro h
  have h' : KSR.zero.srInvariant = ksrOther.srInvariant := by rw [h]
  have : (True : Prop) = False := h'
  exact (this ▸ trivial : False)

/-- A path between any two points in the indiscrete topology. -/
private def indiscretePath (x y : KSR) : @Path KSR ⊤ x y :=
  @Path.mk KSR ⊤ x y
    (@ContinuousMap.mk _ _ _ ⊤ (fun t => if (t : ℝ) = 1 then y else x) continuous_top)
    (by simp) (by simp)

/-- **Honest negative [T1]**: `MorseObstruction` is NOT universal over
topologies. Under `⊤` (every set path-connected) with `F ≡ 0`, the points
`KSR.zero ≠ ksrOther` are two local minima at value `0`, yet every sublevel
is path-connected. This is exactly the statement of the deleted axiom,
negated. -/
theorem morse_obstruction_not_universal :
    ¬ ∀ (t : TopologicalSpace KSR) (F : KSR → ℝ), @MorseObstruction t F := by
  intro h
  letI : TopologicalSpace KSR := ⊤
  have hM : MorseObstruction (fun _ : KSR => (0 : ℝ)) := h ⊤ _
  have hTwo : TwoDistinctMinimaAt (fun _ : KSR => (0 : ℝ)) 0 :=
    ⟨KSR.zero, ksrOther, zero_ne_ksrOther,
      ⟨⟨Set.univ, trivial, isOpen_univ, fun _ _ => le_refl _⟩, rfl⟩,
      ⟨⟨Set.univ, trivial, isOpen_univ, fun _ _ => le_refl _⟩, rfl⟩⟩
  obtain ⟨ε, hε, hnot⟩ := hM 0 hTwo
  apply hnot
  refine ⟨KSR.zero, ?_, fun {y} _ => ⟨indiscretePath KSR.zero y, fun t => ?_⟩⟩
  · show (0 : ℝ) ≤ 0 + ε; linarith
  · show (0 : ℝ) ≤ 0 + ε; linarith

/-! ## Consequence: the Morse-conditional non-connectedness

If `SAGFfunctional` has two distinct local minima at the same
critical value, basin connectivity FAILS.  This is the
acknowledgement-as-theorem.

This is the **structural risk** of the v0.9 line 16763 claim — and
the reason it cannot be discharged without the
at-most-one-local-minimum predicate. -/

/-- **CONDITIONAL** on the named hypothesis `MorseObstruction F` (was an
axiom until 2026-09-10; see `morse_obstruction_not_universal`).

Statement: any `F` satisfying the Morse obstruction and having two distinct
local minima at the same value fails `BasinConnectivity_superseded_conjecture`. -/
theorem basin_connectivity_fails_of_two_minima
    (F : KSR → ℝ) (hM : MorseObstruction F) {cStar : ℝ}
    (h : TwoDistinctMinimaAt F cStar) :
    ¬ BasinConnectivity_superseded_conjecture F := by
  intro h_BC
  obtain ⟨ε, _hε_pos, h_disc⟩ := hM cStar h
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
