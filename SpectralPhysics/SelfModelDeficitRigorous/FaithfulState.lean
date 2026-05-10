/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import SpectralPhysics.SelfModelDeficitRigorous.SectorDecomposition

/-!
# Faithful States on Finite-Dimensional Sector C*-Algebras (Honest)

This file formalizes Axiom 3's conditions (faithfulness and sector
faithfulness) as **predicates on `(A, ω)` pairs** — *not* as axioms
forcing the conclusion of Proposition 23.10.

The earlier deceptive branch (`compute/zetaF-prime-zero`) introduced
axioms that *named* an outcome (e.g. `zeta_regularization_log_sum`
asserting `-ζ̃'_vis(0) = Σ mult · (-log y)` with each summand axiomatised
to a specific rational). Here, every condition we introduce is
* a Prop-valued predicate on `(A, ω)`, with no fixed numerical content;
* an *hypothesis* of downstream theorems, not a conclusion.

## Mathematical content

Let `A = A_vis ⊕ A_hid` be a finite-dimensional *-algebra with a
distinguished sector decomposition.  A faithful state `ω : A → ℝ`
satisfies, by definition, `ω(a* a) > 0` for every nonzero `a ∈ A`.

Axiom 3 of the manuscript has three conditions:
1. **Determination (i)**: the trace determines the spectrum.
2. **Faithfulness (ii)**: `ω(a* a) > 0` for every nonzero `a`.
3. **Sector Faithfulness (iii)**: each tensor factor is independently
   reconstructible — equivalently, partial-trace restrictions are
   faithful on each sector.

For the Self-Model Deficit Theorem, we need:
* `CompletenessAtLevel2` — the trace's one-loop output
  `−ζ̃'_vis(0)` is bounded by hidden-sector capacity
  `dim(H_hid)` (this is exactly Step 3, v0.9 line 8452).
* `SectorFaithfulNoDeadWeight` — every hidden state participates in
  the spectral depth: no hidden state is "dead weight"
  (this is Step 4, v0.9 line 8454).

These predicates are stated as **conditions on numeric capacity vs.
spectral depth**, parameterised by a real-valued `informationContent`
function. The connection to the actual Mellin / heat-kernel pipeline
is then made in `SpectralZeta.lean` by *defining*
`informationContent := −ζ̃'_vis(0)`.

## Honesty checks

* No axiom in this file fixes a numerical value of any sum.
* No axiom in this file asserts the conclusion of Proposition 23.10.
* The predicates `CompletenessAtLevel2` and `SectorFaithfulNoDeadWeight`
  are *general* C*-algebraic conditions that *may or may not hold*
  on a given pair `(A, ω)`.  Whether they hold is the substantive
  question.
-/

namespace SpectralPhysics.SelfModelDeficitRigorous.FaithfulState

open SpectralPhysics.SelfModelDeficitRigorous.SectorDecomposition

/-- A finite-dimensional sectored *-algebra with state.

We use a *bundled* presentation (rather than typeclasses) to keep the
hypothesis set explicit at the proof site.  The role of `state` is the
positive linear functional `ω`; `dimVis` / `dimHid` are the dimensions
of the visible / hidden subspaces.

The integer `dimAlg` records `dim_ℝ(A_vis) + dim_ℝ(A_hid)`.  We do
**not** require any structural relationship between `dimAlg` and the
sector decomposition `(dimVis, dimHid)`; both are parameters. -/
structure SectoredStarAlgebra where
  /-- Carrier of the algebra. -/
  Carrier : Type
  /-- Multiplication on `Carrier`. -/
  mul : Carrier → Carrier → Carrier
  /-- The zero element of `Carrier`. -/
  zero : Carrier
  /-- The involution `*`. -/
  star : Carrier → Carrier
  /-- The positive linear functional `ω : A → ℝ`. -/
  state : Carrier → ℝ
  /-- `ω(a* a) ≥ 0` for every `a`. -/
  state_nonneg : ∀ a : Carrier, state (mul (star a) a) ≥ 0
  /-- Dimension of the visible sector `A_vis`. -/
  dimVis : ℕ
  /-- Dimension of the hidden sector `A_hid`. -/
  dimHid : ℕ

/-- **Faithfulness of `ω`** (Axiom 3, condition ii):
`ω(a* a) > 0` for every nonzero `a ∈ A`. -/
def Faithful (S : SectoredStarAlgebra) : Prop :=
  ∀ a : S.Carrier, a ≠ S.zero → S.state (S.mul (S.star a) a) > 0

/-- **Completeness at Level 2** — the structural form of Step 3.

We parameterise this predicate by a real number `infContent : ℝ`,
intended to be the visible-sector's one-loop information content
(i.e., `−ζ̃'_vis(0)` once it is defined).  The condition says:

  *the hidden-sector capacity `dim(H_hid)` is sufficient to
  accommodate `infContent` units of self-referential information.*

Concretely: `(infContent : ℝ) ≤ (dim H_hid : ℝ)`.

**Why this is the honest formalisation of v0.9 Step 3.**
v0.9 line 8452 says: "If the capacity is insufficient, the self-model
cannot store the visible sector's full one-loop information, and the
trace restricted to the self-model fails to be faithful at Level 2."
Logically that is: *faithfulness at Level 2* implies
`infContent ≤ dim H_hid`. We bundle that implication into the
predicate itself — making the bound a hypothesis, not a conclusion. -/
def CompletenessAtLevel2 (S : SectoredStarAlgebra) (infContent : ℝ) : Prop :=
  (infContent : ℝ) ≤ (S.dimHid : ℝ)

/-- **Sector Faithfulness — no hidden state is dead weight**
(structural form of Step 4).

Again parameterised by `infContent : ℝ`, intended to be `−ζ̃'_vis(0)`.
The condition says:

  *every hidden-sector state participates in the visible spectrum's
  information content; no hidden state is invisible to the trace.*

Concretely: `(dim H_hid : ℝ) ≤ (infContent : ℝ)`.

**Why this is the honest formalisation of v0.9 Step 4.**
v0.9 line 8454 says: "If `dim(H_hid) > −ζ̃'_vis(0)`, excess hidden
states carry no self-referential information about the visible
sector — they are dead weight, invisible to the trace's
self-referential content. This violates sector faithfulness."
Logically: *sector faithfulness with no dead weight* implies
`dim H_hid ≤ infContent`. -/
def SectorFaithfulNoDeadWeight
    (S : SectoredStarAlgebra) (infContent : ℝ) : Prop :=
  (S.dimHid : ℝ) ≤ (infContent : ℝ)

/-- The conjunction: **a sectored algebra satisfies Axiom 3's
completeness-plus-sector-faithfulness at level 2 with respect to
`infContent`** iff both bounds hold. -/
def Axiom3Level2 (S : SectoredStarAlgebra) (infContent : ℝ) : Prop :=
  CompletenessAtLevel2 S infContent ∧ SectorFaithfulNoDeadWeight S infContent

/-- **Trivial structural lemma** (not the headline; just bookkeeping):
if both bounds hold, then `infContent = dim(H_hid)`.

This is exactly Step 5 (`≥` + `≤` → `=`). -/
theorem dim_hid_eq_of_axiom3_level2
    (S : SectoredStarAlgebra) (infContent : ℝ)
    (h : Axiom3Level2 S infContent) :
    (S.dimHid : ℝ) = infContent := by
  rcases h with ⟨h_le, h_ge⟩
  -- h_le : infContent ≤ dimHid    (completeness)
  -- h_ge : dimHid    ≤ infContent (sector faithfulness)
  exact le_antisymm h_ge h_le

/-! ### Honesty: what the predicates do *not* claim

The predicates `CompletenessAtLevel2` and `SectorFaithfulNoDeadWeight`
are *real-valued inequalities* that **must be supplied as hypotheses**
to the downstream theorems.  They are not theorems of this file.

In particular:

* We do **not** assert "every faithful state on a finite-dimensional
  C*-algebra with sector decomposition satisfies both bounds." That
  is exactly what v0.9 line 8464 flags as the open problem.
* We do **not** axiomatise `−ζ̃'_vis(0)` to any specific real value.
* We do **not** assume any specific Yukawa values.

What this file *does* provide:

* A precise predicate-level statement of the structural form of
  Steps 3 and 4.
* A trivial Step-5 combiner (`dim_hid_eq_of_axiom3_level2`) that
  packages "`≥` and `≤` ⇒ equality" using `le_antisymm`.

The substantive question — does Axiom 3 force `Axiom3Level2 S
(−ζ̃'_vis(0))` for the spectral-physics algebra `S`? — is left to
the downstream modules `CompletenessBound.lean` and
`FaithfulnessBound.lean`, and is honestly flagged as open. -/

end SpectralPhysics.SelfModelDeficitRigorous.FaithfulState
