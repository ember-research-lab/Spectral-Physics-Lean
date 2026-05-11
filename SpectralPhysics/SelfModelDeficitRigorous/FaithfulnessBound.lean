/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SelfModelDeficitRigorous.SectorDecomposition
import SpectralPhysics.SelfModelDeficitRigorous.FaithfulState
import SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta

/-!
# Step 4: Faithfulness Upper Bound `dim(H_hid) ≤ −ζ̃'_vis(0)` (Honest)

This file formalises **Step 4** of v0.9 Proposition 23.10
(line 8454): from Axiom 3 condition (iii) — *sector faithfulness*
(no dead-weight hidden states) — derive

    dim(H_hid) ≤ −ζ̃'_vis(0).

## The argument, restated

v0.9 line 8454:
> "Axiom 3(iii) requires sector faithfulness: every degree of
> freedom participates. If `dim(H_hid) > −ζ̃'_vis(0)`, excess hidden
> states carry no self-referential information about the visible
> sector — they are dead weight, invisible to the trace's
> self-referential content. This violates sector faithfulness:
> `dim(H_hid) ≤ −ζ̃'_vis(0)`."

## The honest theorem

Symmetric to `CompletenessBound.lean`. We provide:

* A **structural lemma**: if `SectorFaithfulNoDeadWeight S
  (−ζ̃'_vis(0))` holds, then `dim(H_hid) ≤ −ζ̃'_vis(0)`. This is
  a definitional unfolding.
* A **contrapositive lemma**: if `dim(H_hid) > −ζ̃'_vis(0)`, then
  `SectorFaithfulNoDeadWeight` fails — this is the "dead weight
  violation pathway".

What we honestly do NOT do:

* Derive `SectorFaithfulNoDeadWeight` from `SectorFaithful` of
  `SpectralPhysics.Axioms.SelfRefClosure` for the spectral-physics
  algebra `S`. That derivation requires the same Level-2 / heat-kernel
  formalisation infrastructure as Step 3, and is **open** (v0.9
  line 8464).
* Axiomatise `dim(H_hid) ≤ −ζ̃'_vis(0)` for any specific `(S, V)`.

## Smuggling check

* No axiom in this file forces `−ζ̃'_vis(0)` to a specific value.
* No axiom in this file forces `dim(H_hid)` to a specific value.
* The bound is *conditional* on a Prop-valued hypothesis that the
  caller must supply.
-/

namespace SpectralPhysics.SelfModelDeficitRigorous.FaithfulnessBound

open SpectralPhysics.SelfModelDeficitRigorous.SectorDecomposition
open SpectralPhysics.SelfModelDeficitRigorous.FaithfulState
open SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta

variable (S : SectoredStarAlgebra) (V : VisibleSpectrum)

/-- **Step 4 (forward / structural form)**:
If the sectored algebra `S` satisfies sector faithfulness with no
dead-weight hidden states relative to the visible sector's spectral
depth `−ζ̃'_vis(0)`, then `dim(H_hid) ≤ −ζ̃'_vis(0)`.

**Status**: like `completeness_lower_bound`, this is a definitional
unfolding of `SectorFaithfulNoDeadWeight`.  The substantive content
has been pushed into the hypothesis `h`. -/
theorem sector_faithfulness_upper_bound
    (h : SectorFaithfulNoDeadWeight S (negZetaPrimeAtZero V)) :
    (S.dimHid : ℝ) ≤ negZetaPrimeAtZero V := h

/-- **Step 4 (contrapositive)**:
If the hidden capacity exceeds the spectral depth `−ζ̃'_vis(0)`,
then Axiom 3(iii) sector faithfulness fails on `(S, V)`.

This is the contrapositive of `sector_faithfulness_upper_bound`,
and is the **precise form of v0.9 line 8454's "...excess hidden
states ... are dead weight, invisible to the trace's self-referential
content."** -/
theorem sector_faithfulness_fails_of_dead_weight
    (h_violate : negZetaPrimeAtZero V < (S.dimHid : ℝ)) :
    ¬ SectorFaithfulNoDeadWeight S (negZetaPrimeAtZero V) := by
  intro h
  -- h : S.dimHid ≤ negZetaPrimeAtZero V
  -- h_violate : negZetaPrimeAtZero V < S.dimHid
  exact (not_lt.mpr h) h_violate

/-- **Step 4 (in the `informationContent` formulation)**:
expanded form of `sector_faithfulness_upper_bound` where
`negZetaPrimeAtZero V` is replaced by `informationContent V`. -/
theorem sector_faithfulness_upper_bound_explicit
    (h : SectorFaithfulNoDeadWeight S (negZetaPrimeAtZero V)) :
    (S.dimHid : ℝ) ≤ informationContent V := by
  have h_eq := negZetaPrimeAtZero_eq V
  rw [← h_eq]
  exact h

/-! ### Honest open-problem flag

The substantive question — "does the spectral-physics finite C*-
algebra `(A_obs, ω)` with sector decomposition `H_vis ⊕ H_hid`,
under Axiom 3(iii), satisfy `SectorFaithfulNoDeadWeight S
(−ζ̃'_vis(0))`?" — is **not proved in this file**, and the v0.9
manuscript itself (line 8464) flags it as part of the open
formalisation problem.

What is open:

1. A precise C*-algebraic statement of "no dead-weight hidden
   state" that goes beyond GNS faithfulness on the whole algebra to
   capture the *partial-trace* level reconstructibility.
2. A theorem deriving `SectorFaithfulNoDeadWeight` from
   `SpectralPhysics.Axioms.SelfRefClosure.SectorFaithful`
   plus the heat-kernel / Mellin pipeline.  -/

end SpectralPhysics.SelfModelDeficitRigorous.FaithfulnessBound
