/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SelfModelDeficitRigorous.SectorDecomposition
import SpectralPhysics.SelfModelDeficitRigorous.FaithfulState
import SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta

/-!
# Step 3: Completeness Lower Bound `dim(H_hid) ≥ −ζ̃'_vis(0)` (Honest)

This file formalises **Step 3** of v0.9 Proposition 23.10
(line 8452): from Axiom 3 condition (ii) — the *completeness* of the
trace as a self-model — derive

    dim(H_hid) ≥ −ζ̃'_vis(0).

## The argument, restated

v0.9 line 8452:
> "Axiom 3(ii) requires the trace to detect every nonzero element of
> A_obs. At one loop, the trace produces ζ̃'_vis(0) — the visible
> sector's spectral depth. For the self-model to faithfully represent
> this depth, it must have sufficient capacity:
> `dim(H_hid) ≥ −ζ̃'_vis(0)`. If the capacity is insufficient, the
> self-model cannot store the visible sector's full one-loop
> information, and the trace restricted to the self-model fails to be
> faithful at Level 2."

Two distinct directions of the implication are needed:

* (forward) "Capacity sufficient ⇒ bound holds": this is the
  predicate definition `CompletenessAtLevel2` from `FaithfulState.lean`.
* (contrapositive) "Bound violated ⇒ capacity insufficient ⇒ the trace
  fails to be faithful at Level 2 in the self-model": this is
  exactly v0.9's argument (line 8452).

## The honest theorem

We **do not** try to prove "Axiom 3(ii) ⇒ bound holds" from Mathlib's
existing C*-algebra infrastructure: the *physical content* of Axiom 3
(self-model faithfulness at Level 2 of the loop expansion) is not yet
formalised in Lean. Instead we provide:

* A **structural lemma**: if `CompletenessAtLevel2 S (−ζ̃'_vis(0))`
  holds, then `−ζ̃'_vis(0) ≤ dim(H_hid)`. This is a trivial
  unfolding — but it is exactly what `CompletenessAtLevel2` was
  defined to mean.
* A **contrapositive lemma**: if `−ζ̃'_vis(0) > dim(H_hid)`, then
  `CompletenessAtLevel2` fails (capacity insufficient). This is the
  "violation pathway".

What is *not* in this file (and is honestly flagged as open):

> An operator-algebraic derivation of `CompletenessAtLevel2` from
> the abstract C*-algebraic faithfulness of a state on a finite-dim
> sectored algebra. This requires formalising the one-loop /
> Level-2 information condition, which v0.9 itself (line 8464) calls
> the **open formalisation problem**.

## Smuggling check

* No axiom in this file forces `−ζ̃'_vis(0)` to a specific value.
* No axiom in this file forces `dim(H_hid)` to a specific value.
* The bound is *conditional* on a Prop-valued hypothesis that the
  caller must supply.
-/

namespace SpectralPhysics.SelfModelDeficitRigorous.CompletenessBound

open SpectralPhysics.SelfModelDeficitRigorous.SectorDecomposition
open SpectralPhysics.SelfModelDeficitRigorous.FaithfulState
open SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta

variable (S : SectoredStarAlgebra) (V : VisibleSpectrum)

/-- **Step 3 (forward / structural form)**:
If the sectored algebra `S` satisfies the level-2 completeness
condition with respect to the visible sector's spectral depth
`−ζ̃'_vis(0)`, then `−ζ̃'_vis(0) ≤ dim(H_hid)`.

**Status**: this is a definitional unfolding of
`CompletenessAtLevel2`.  The substantive content has been pushed
into the hypothesis `h`; the proof here is `id` plus the `≤` direction
of the predicate.  This is honest: we are not pretending to derive
the bound from Mathlib; we are stating it as a conditional theorem
whose hypothesis is exactly the v0.9 "completeness at level 2"
condition. -/
theorem completeness_lower_bound
    (h : CompletenessAtLevel2 S (negZetaPrimeAtZero V)) :
    negZetaPrimeAtZero V ≤ (S.dimHid : ℝ) := h

/-- **Step 3 (contrapositive)**:
If the spectral depth `−ζ̃'_vis(0)` *exceeds* the hidden capacity
`dim(H_hid)`, then Axiom 3(ii) completeness at Level 2 fails on
`(S, V)`.

This is the contrapositive of `completeness_lower_bound`, and is the
**precise form of v0.9 line 8452's "...the trace restricted to the
self-model fails to be faithful at Level 2."**

The mathematical content is the equivalence
`¬ (a ≤ b) ↔ b < a`. -/
theorem completeness_fails_of_capacity_insufficient
    (h_violate : (S.dimHid : ℝ) < negZetaPrimeAtZero V) :
    ¬ CompletenessAtLevel2 S (negZetaPrimeAtZero V) := by
  intro h
  -- h : negZetaPrimeAtZero V ≤ S.dimHid
  -- h_violate : S.dimHid < negZetaPrimeAtZero V
  exact (not_lt.mpr h) h_violate

/-- **Step 3 (in the `informationContent` formulation)**:
expanded form of `completeness_lower_bound` where we replace
`negZetaPrimeAtZero V` by its definitional equal
`informationContent V`. -/
theorem completeness_lower_bound_explicit
    (h : CompletenessAtLevel2 S (negZetaPrimeAtZero V)) :
    informationContent V ≤ (S.dimHid : ℝ) := by
  have h_eq := negZetaPrimeAtZero_eq V
  -- h_eq : negZetaPrimeAtZero V = informationContent V
  rw [← h_eq]
  exact h

/-! ### Honest open-problem flag

The substantive question — "does the spectral-physics finite C*-
algebra `(A_obs, ω)` with sector decomposition `H_vis ⊕ H_hid`,
under Axiom 3(ii), satisfy `CompletenessAtLevel2 S (−ζ̃'_vis(0))`?" —
is **not proved in this file**, and the v0.9 manuscript itself
(line 8464) flags it as the open formalisation problem.

What is open:

1. A precise C*-algebraic definition of "Level-2 self-model
   faithfulness" beyond the GNS-faithfulness already in Mathlib.
2. A theorem deriving `CompletenessAtLevel2` from that definition
   plus the heat-kernel / Mellin pipeline.

What we do NOT do (and an audit would catch us doing):

* We do **not** introduce an axiom `axiom completeness_holds`
  asserting `CompletenessAtLevel2 S (...)` for the specific
  spectral-physics `S`.
* We do **not** axiomatise `negZetaPrimeAtZero V = 288` for any
  specific `V`.  -/

end SpectralPhysics.SelfModelDeficitRigorous.CompletenessBound
