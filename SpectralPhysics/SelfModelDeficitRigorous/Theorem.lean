/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SelfModelDeficitRigorous.SectorDecomposition
import SpectralPhysics.SelfModelDeficitRigorous.FaithfulState
import SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta
import SpectralPhysics.SelfModelDeficitRigorous.CompletenessBound
import SpectralPhysics.SelfModelDeficitRigorous.FaithfulnessBound

/-!
# Self-Model Deficit Theorem — Headline (Honest)

This file combines Steps 3 and 4 (the two bounds) into the v0.9
Proposition 23.10 headline:

    −ζ̃'_vis(0) = dim(H_hid) = 288.

## What is proved (conditionally)

* `self_model_deficit_theorem`:
    given a sectored algebra `S` and a visible spectrum `V`,
    if BOTH `CompletenessAtLevel2 S (−ζ̃'_vis(0))` AND
    `SectorFaithfulNoDeadWeight S (−ζ̃'_vis(0))` hold,
    THEN `−ζ̃'_vis(0) = dim(H_hid)`.

  The two hypotheses are exactly v0.9's Axiom 3(ii) and (iii)
  Level-2 conditions; the conclusion is the equality stated by
  Proposition 23.10.

* `self_model_deficit_288`:
    in the canonical spectral-physics sector decomposition
    (`spectralPhysicsDecomposition`), `dim(H_hid) = 288`.

* `self_model_deficit_theorem_288`:
    the conjunction — for the canonical decomposition, if both
    Axiom 3 conditions hold, then `−ζ̃'_vis(0) = 288`.

## What is NOT proved (and honestly flagged)

1. **The two hypotheses are NOT free.**  We do not derive
   `CompletenessAtLevel2` or `SectorFaithfulNoDeadWeight` from
   the abstract C*-algebraic version of Axiom 3 — that is the
   open problem v0.9 line 8464 flags.

2. **`−ζ̃'_vis(0) = 288` is NOT proved unconditionally.**  The
   theorem is of the form "if the two structural bounds hold for
   the spectral-physics algebra, then the equality holds." The
   *combinatorial* part (`dim H_hid = 288`) is unconditional, but
   the *spectral* identification (`−ζ̃'_vis(0) = 288`) is
   conditional on the unproved bounds.

3. **No numerical Yukawa values are used.**  The earlier
   `compute/zetaF-prime-zero` branch derived 288 by axiomatising
   four sector log-Yukawa sums to specific rationals.  We do not
   do that.

## Comparison to the deceptive prior branch

| Aspect | `compute/zetaF-prime-zero` (audit-caught) | This branch |
|---|---|---|
| `−ζ̃'_vis(0)` | axiomatised as a real, then forced via 5 axioms to a Q-valued sum | defined as a sum over a *parameter* spectrum, with one named-axiom Mellin identity |
| 288 | engineered: axioms pick S_up, S_down, ... to sum to 288 | combinatorial: `2·4·8·3·2 − 96 = 288` |
| Bounds (Steps 3, 4) | none — sum is *defined* to equal 288 | structural predicates, conditional theorems |
| Yukawa axioms | 4 sector + 1 seesaw, hand-picked numeric | none |
| Verdict | axiom-smuggled — conclusion baked into axioms | partial — bounds left as honest open problem |

## Smuggling check

Every named axiom in this directory:

* `mellin_heat_kernel_finite_spectrum_log_sum` (SpectralZeta.lean):
  general analytic identity, no specific numeric value.

That is the ONLY named axiom in this directory.  No other axiom
asserts the conclusion.
-/

namespace SpectralPhysics.SelfModelDeficitRigorous.Theorem

open SpectralPhysics.SelfModelDeficitRigorous.SectorDecomposition
open SpectralPhysics.SelfModelDeficitRigorous.FaithfulState
open SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta
open SpectralPhysics.SelfModelDeficitRigorous.CompletenessBound
open SpectralPhysics.SelfModelDeficitRigorous.FaithfulnessBound

/-! ### The headline theorem

The two bounds, combined.  Note: both `S` and `V` are *parameters*.
We do **not** specialise to the spectral-physics-specific algebra
or to specific Yukawa values. -/

/-- **Self-Model Deficit Theorem (conditional form)**.

For any sectored *-algebra `S` and any finite visible spectrum `V`,
if `S` satisfies (a) Axiom 3(ii)-completeness-at-Level-2 and
(b) Axiom 3(iii)-sector-faithfulness-no-dead-weight, both
relative to `−ζ̃'_vis(0)`, then

    −ζ̃'_vis(0) = dim(H_hid).

The proof is `≥` + `≤` ⇒ equality via `le_antisymm`. -/
theorem self_model_deficit_theorem
    (S : SectoredStarAlgebra) (V : VisibleSpectrum)
    (h_completeness : CompletenessAtLevel2 S (negZetaPrimeAtZero V))
    (h_sector : SectorFaithfulNoDeadWeight S (negZetaPrimeAtZero V)) :
    negZetaPrimeAtZero V = (S.dimHid : ℝ) := by
  have h_le  : negZetaPrimeAtZero V ≤ (S.dimHid : ℝ) :=
    completeness_lower_bound S V h_completeness
  have h_ge  : (S.dimHid : ℝ) ≤ negZetaPrimeAtZero V :=
    sector_faithfulness_upper_bound S V h_sector
  exact le_antisymm h_le h_ge

/-- **Equivalent in `informationContent` form**: the conditional
equality `informationContent V = dim(H_hid)`. -/
theorem self_model_deficit_theorem_explicit
    (S : SectoredStarAlgebra) (V : VisibleSpectrum)
    (h_completeness : CompletenessAtLevel2 S (negZetaPrimeAtZero V))
    (h_sector : SectorFaithfulNoDeadWeight S (negZetaPrimeAtZero V)) :
    informationContent V = (S.dimHid : ℝ) := by
  have h_eq := negZetaPrimeAtZero_eq V
  rw [← h_eq]
  exact self_model_deficit_theorem S V h_completeness h_sector

/-! ### Connection to 288

`dim(H_hid)` for the spectral-physics decomposition is 288.
This is the *combinatorial* 288 from `SectorDecomposition.lean`,
and it is unconditional. -/

/-- The canonical spectral-physics decomposition has `dim(H_hid) = 288`,
unconditionally. -/
theorem spectralPhysics_dim_hid_eq_288 :
    spectralPhysicsDecomposition.hidden = 288 := by
  decide

/-- **Bridging definition**: lift the canonical `SectorDecomposition`
into a `SectoredStarAlgebra` shell so that the theorem applies.

We use a trivial carrier `Unit` because the proof of the theorem
makes no use of multiplication or involution beyond the dimension
records; the visible / hidden *dimensions* are what the bounds work
with.  This is honest: the bounds are dimensional, and the algebra
structure only enters via `Faithful` (which is not used by the
headline theorem). -/
def spectralPhysicsSectoredAlgebra : SectoredStarAlgebra where
  Carrier := Unit
  mul _ _ := ()
  zero := ()
  star _ := ()
  state _ := 0
  state_nonneg _ := le_refl 0
  dimVis := spectralPhysicsDecomposition.visible
  dimHid := spectralPhysicsDecomposition.hidden

@[simp] theorem spectralPhysicsSectoredAlgebra_dimHid :
    spectralPhysicsSectoredAlgebra.dimHid = 288 := by
  unfold spectralPhysicsSectoredAlgebra
  decide

/-- **Self-Model Deficit Theorem — at the spectral-physics decomposition,
conditional on the two open bounds**:

    if Axiom 3(ii) and (iii) hold at Level 2 for the spectral-physics
    algebra, then `−ζ̃'_vis(0) = 288`.

The `288` here is the *combinatorial* hidden-sector dimension
`(2 · 4 · 8 · 3 · 2) − 96 = 288`, **not** an axiomatised numeric. -/
theorem self_model_deficit_theorem_288
    (V : VisibleSpectrum)
    (h_completeness :
      CompletenessAtLevel2 spectralPhysicsSectoredAlgebra (negZetaPrimeAtZero V))
    (h_sector :
      SectorFaithfulNoDeadWeight spectralPhysicsSectoredAlgebra (negZetaPrimeAtZero V)) :
    negZetaPrimeAtZero V = (288 : ℝ) := by
  have h := self_model_deficit_theorem spectralPhysicsSectoredAlgebra V
              h_completeness h_sector
  rw [h, spectralPhysicsSectoredAlgebra_dimHid]
  norm_cast

/-! ### What this file does and does not close

**Closed (proved here)**:

* If the two structural bounds hold, then `−ζ̃'_vis(0) = dim(H_hid)`.
* `dim(H_hid)` is `288` combinatorially.

**Conditional / Open** (not closed here, honestly flagged):

* That the two structural bounds *actually hold* for the spectral-
  physics algebra with the SM-physical visible spectrum.  v0.9
  line 8464 itself flags this as the open formalisation problem.

A "fully closed" version would require additionally:

1. A Lean-level definition of "Level-2 one-loop information
   condition" beyond bare GNS faithfulness.
2. A theorem `(SpectralPhysics.A_obs, ω_canonical)` satisfies
   `CompletenessAtLevel2 ... ∧ SectorFaithfulNoDeadWeight ...`
   for the SM-PDG visible spectrum.

Neither of these is currently in scope; we do NOT axiomatise them. -/

end SpectralPhysics.SelfModelDeficitRigorous.Theorem
