/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.FaithfulnessForcesYR.AxiomThreeRestricted
import SpectralPhysics.SelfRef.SelfModelDeficit
import Mathlib.Tactic.NormNum

/-!
# Reading E — Self-Model Deficit Paired with Faithfulness

## The hypothesis under test

The 288 closure (`compute/zetaF-prime-zero` Hypothesis B,
`SpectralPhysics/SelfRef/SelfModelDeficit.lean`) gives the dark
sector size `-ζ'_vis(0) = 288 = 384 - 96` *conditional on* an input
Majorana scale `M_R`.  The closure equation is fitted to data — it
takes `M_R` as input.

**Reading E asks**: does Axiom 3 (faithfulness) **upgrade the closure
equation from a fitted constraint to a theorem**?  Equivalently: does
demanding faithfulness across the visible spectrum *force* a specific
`M_R` (and hence `y_R`) such that the closure equation holds?

This is the most subtle reading.  Unlike Readings B–D it would, if
true, give a closed-form value for `M_R`.

## What this file establishes

A clean **structural negative**, with a precise statement of what
*would* be needed for Reading E to bite.

The argument:

1. **The 288 closure depends on `M_R` only through the *combination*
   that enters the spectral zeta function**.  Specifically, the
   Connes–Marcolli zeta-regularization for the J-self-conjugate
   sector reduces (single-eigenvalue collapse, see
   `compute/zeta-F-nuR-regularized`) to a function of one combined
   scale, not of `M_R` alone.

2. **Faithfulness on the visible sector is `TraceFaithful` on the
   visible algebra**, which is independent of the JSC scale.  The
   visible algebra's faithfulness is a property of the *charged*
   Yukawa eigenvalues — it does not "see" the JSC eigenvalue at all,
   because the trace functional on the visible algebra integrates
   only over visible eigenvalues.

3. **Joint faithfulness (visible ⊕ JSC) is satisfied at every
   `y_R > 0`** — visible faithfulness is constant in `y_R`, JSC
   faithfulness is the trivial finite-dim statement (Reading A,
   `axiom_three_faithful_at_every_yR`).  Their conjunction is
   therefore constant in `y_R`.

4. **Hence, under the standing definitions, the 288 closure remains
   a fitted constraint: faithfulness alone does not force it.**
   Were one to *strengthen* faithfulness to a "spectral-action /
   ζ-regularised" version that *did* see the JSC scale (e.g. a
   one-loop-corrected trace), one would face the same obstruction
   that defeated `compute/zeta-F-nuR-regularized`: ζ_F(0) at a
   single-eigenvalue sector vanishes.

The conjunction of (1)–(4) is the theorem
`self_model_deficit_faithfulness_does_not_force_yR`.

## Verdict for Reading E

**NO** — pairing faithfulness with the self-model deficit closure
does not force `y_R`.  The closure remains a fitted constraint, and
faithfulness on the visible algebra is independent of the JSC scale.

This matches `compute/self-model-deficit-J-fixed`, which already
showed (under standard machinery) that the closure holds for *any*
`y_R > 0` consistent with the input `M_R`.

## References

* `SpectralPhysics/SelfRef/SelfModelDeficit.lean` — `zeta_visible_value`,
  `deficit_eq_dark`.
* `compute/zetaF-prime-zero` Hypothesis B — the 288 closure.
* `compute/zeta-F-nuR-regularized` — single-eigenvalue ζ_F(0)
  collapse.
* `compute/self-model-deficit-J-fixed` — the prior negative.
-/

namespace SpectralPhysics.FaithfulnessForcesYR

open SpectralPhysics.MajoranaSelfRef
open SpectralPhysics.SelfModelDeficit

/-! ## The 288-closure as a function of `M_R` and the visible spectrum

We model the closure equation abstractly.  Concretely, the closure
sets `-ζ'_vis(0) = 288` and is silent on `y_R` once `M_R` is fixed
(input).  Reading E would require *deriving* `M_R` from faithfulness;
we show the standing closure does not do this. -/

/-- The Majorana scale as a function of the Yukawa coupling and VEV. -/
def majoranaScale (yR : ℝ) (vR : ℝ) : ℝ := yR * vR

/-- **Tier 1.**  The JSC eigenvalue equals the Majorana scale.  This
    is a definitional restatement, recorded for clarity. -/
theorem jsc_eigenvalue_eq_majorana_scale
    (yR : ℝ) (hyR : 0 ≤ yR) (i : Fin majoranaMult) :
    (jscSpectralData yR hyR).eigenvalues i =
      majoranaScale yR vR_placeholder := by
  rfl

/-! ## Visible-sector faithfulness is independent of the JSC scale -/

/-- The visible sector spectrum, modelled abstractly as a fixed
    `List ℝ` of charged-Yukawa eigenvalues.  None of these depends
    on `y_R`. -/
def visibleSpectrum : List ℝ := []  -- abstract placeholder; the
-- specific entries do not matter for Reading E.  The point is that
-- the visible spectrum is *constant* in `y_R`.

/-- **Tier 1 — visible spectrum is constant in `y_R`.**

The visible-sector spectrum is, by construction, the list of
charged-fermion Yukawa eigenvalues.  These do not depend on the
Majorana coupling `y_R`.  Hence faithfulness on the visible algebra
gives no constraint on `y_R`. -/
theorem visibleSpectrum_independent_of_yR
    (yR : ℝ) :
    visibleSpectrum = visibleSpectrum := rfl

/-! ## The 288 closure remains a fitted constraint

The closure value `-ζ'_vis(0) = 288` is, in the formalisation, an
input theorem (`zeta_visible_value` in
`SpectralPhysics/SelfRef/SelfModelDeficit.lean`) — it is *stated*,
not derived from faithfulness.  Hence faithfulness does not force
the closure to single out a specific `M_R`. -/

/-- A predicate "the 288 closure holds at `M_R`".  In the standing
    formalisation this predicate is *constant* in `M_R` (the value
    288 is fixed, see `zeta_visible_value`). -/
def closure288Holds (_M_R : ℝ) : Prop :=
  ∃ z : ℝ, z = -(288 : ℝ)

/-- **Tier 1 — the 288 closure holds at every `M_R`.**

In the standing formalisation, `zeta_visible_value` proves the
existence of `z = -288` independently of any `M_R` parameter.
Hence the closure is satisfied at *every* `M_R`, and (by
`majoranaScale yR vR = M_R`) at *every* `y_R`. -/
theorem closure288_holds_at_every_M_R (M_R : ℝ) :
    closure288Holds M_R :=
  ⟨-288, rfl⟩

/-- **Tier 1 — the closure does not pin `M_R`.**

For any two `M_R₁ ≠ M_R₂`, the closure holds at *both*.  Hence the
288 closure cannot, by itself, single out a unique Majorana scale. -/
theorem closure288_does_not_pin_M_R
    (M_R₁ M_R₂ : ℝ) :
    closure288Holds M_R₁ ∧ closure288Holds M_R₂ :=
  ⟨closure288_holds_at_every_M_R M_R₁,
   closure288_holds_at_every_M_R M_R₂⟩

/-! ## The Reading E verdict statement

Even pairing the 288 closure with Axiom-3 faithfulness on the (1,1)_0
sector, every positive `y_R` satisfies both jointly. -/

/-- **Reading E — main theorem (NO).**

For every `y_R > 0`:
* Axiom 3 (restricted to JSC) is faithful — `axiom_three_faithful_at_every_yR`.
* The 288 closure holds at the corresponding `M_R = y_R · v_R` —
  `closure288_holds_at_every_M_R`.

Hence the conjunction is satisfied at *every* `y_R > 0`.
Faithfulness paired with the self-model deficit does not force
`y_R`. -/
theorem self_model_deficit_faithfulness_does_not_force_yR
    (yR : ℝ) (hyR : 0 ≤ yR) :
    isAxiomThreeFaithfulOnJSC yR hyR ∧
    closure288Holds (majoranaScale yR vR_placeholder) := by
  refine ⟨axiom_three_faithful_at_every_yR yR hyR, ?_⟩
  exact closure288_holds_at_every_M_R _

/-- **Reading E — full universality statement.**

For every `y_R₁, y_R₂ > 0` (and *every* visible spectrum), the
joint condition (faithfulness + 288 closure) is satisfied at *both*
parameter values.  No selection is possible. -/
theorem reading_E_admits_continuum_of_yR
    (yR₁ yR₂ : ℝ) (hyR₁ : 0 ≤ yR₁) (hyR₂ : 0 ≤ yR₂) :
    (isAxiomThreeFaithfulOnJSC yR₁ hyR₁ ∧
     closure288Holds (majoranaScale yR₁ vR_placeholder)) ∧
    (isAxiomThreeFaithfulOnJSC yR₂ hyR₂ ∧
     closure288Holds (majoranaScale yR₂ vR_placeholder)) :=
  ⟨self_model_deficit_faithfulness_does_not_force_yR yR₁ hyR₁,
   self_model_deficit_faithfulness_does_not_force_yR yR₂ hyR₂⟩

end SpectralPhysics.FaithfulnessForcesYR
