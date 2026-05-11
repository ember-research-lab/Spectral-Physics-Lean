/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.ZetaFNuR.JRestrictedZeta
import SpectralPhysics.ZetaFNuR.ResidueAtZero
import SpectralPhysics.SelfModelDeficit.Yukawas
import SpectralPhysics.SelfModelDeficit.SeeSawCancel
import SpectralPhysics.SelfModelDeficit.ZetaPrimeZero
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# `ζ_F(0; ν_R)` ↔ the 288 closure: does the J-restriction force `y_R`?

This file tests the load-bearing question: *given* the value
`ζ_F(0; ν_R) = mult` (Tier-1 result of `ResidueAtZero.lean`), does
the closure equation

  `−ζ̃'_vis(0) = 288`

force `y_R` to a specific magnitude when combined with the
J-restriction?

## Setup

The full `−ζ̃'_vis(0) = 288` closure decomposes as

  `S_charged + S_νL + S_νR = 288`,

where `S_νR` is the heavy-neutrino contribution to the visible
ζ′(0) sum.  In the framework's convention (Hypothesis B; standard
NCG), `S_νR` carries the multiplicity-6 weight on a single Yukawa
`y_R`:

  `S_νR = -6 · log y_R - 6 · log y_R - ...` (a 3-gen sum
                                            with M_R-dependence
                                            cancelled by see-saw).

The `compute/zetaF-prime-zero` branch encodes `S_νR = -174.01` as
a Tier-2 axiom, with `M_R` adjusted to make the table close exactly
to 288.  The hypothesis under test is whether the J-restriction
*replaces* this Tier-2 input with a derivation.

## Result

**The J-restriction does NOT force `y_R`.**  At `s = 0`, the
J-restricted ζ-function carries only the multiplicity; at the
derivative `s ↦ ζ'_F(s; ν_R)|_{s=0}`, it gives
`-2 · mult · log y_R`, which is structurally the *same* quantity
already used in the 288 closure (under multiplicity 6 it's
`-12 log y_R`, vs. the framework's per-generation 3-gen sum;
they differ by a factor of 2 from the see-saw doubling).

The "structural integer 8" target is *not* recovered: the
multiplicity is 6 (Hypothesis B) or 1 (Hypothesis A), neither
equals 8.  Hence the τ^8 conjecture is *not* forced by the
J-restricted ζ-function.

## What this file proves

* Tier-1: the algebraic relation `ζ_F(0; ν_R) = mult ≠ 8`, and the
  closure equation `S_νR = ζ'_F(0; ν_R) - <stuff>` does not gain
  any new constraint from the J-restriction.

* Tier-2 axioms re-used: ζ-regularization → log-sum reduction
  (`zeta_regularization_log_sum`); the see-saw closed form
  (`seesaw_product_independence`).

## References

* `compute/zetaF-prime-zero` branch's `SelfModelDeficit/` files
  (the existing 288 closure under Hypothesis B).
* `compute/majorana-block-residue` branch's `Discriminator.lean`
  (Hypothesis A vs B; the multiplicity choice).
* Connes–Marcolli (2008) §1.7.4 (the ζ-reg → log-sum identity).
-/

namespace SpectralPhysics.ZetaFNuR

open Real
open SpectralPhysics.SelfModelDeficit
open SpectralPhysics.MajoranaBlock

/-! ## The closure equation under the J-restriction -/

/-- The hypothetical closure: given the value of `ζ_F(0; ν_R)`, can it
    fix `y_R`?  Mathematically:

      `(value of ζ_F(0; ν_R)) · X(y_R) = 288`,

    for some functional `X` of `y_R`.  Since the value is a
    multiplicity-only integer, this becomes

      `mult · X(y_R) = 288`,

    which fixes `X(y_R) = 288/mult` — but `X` here is the rest of
    the visible ζ′(0) sum (charged + light ν), not `−log y_R`
    directly.  The functional form does NOT separate `y_R`. -/
noncomputable def closure_constraint (mult : ℕ) (y_R : ℝ) : Prop :=
  (mult : ℝ) * (-Real.log y_R) = 288 - S_charged - S_nuL

/-! ## Numerical baseline of the closure equation

From the existing branch, with `S_charged + S_nuL = 462.01` and
`S_νR = -174.01`, we have `288 = 462.01 + (-174.01)`, so the closure
already holds with `S_νR = -174.01` independent of any J-restriction. -/

/-- The numerical RHS: `288 - S_charged - S_nuL = S_νR = -174.01`.

    This is just a re-arrangement of `seeSaw_closure` from
    `SelfModelDeficit/SeeSawCancel.lean`. -/
theorem closure_RHS_eq_S_nuR :
    (288 : ℝ) - S_charged - S_nuL = S_nuR := by
  have h := seeSaw_closure
  linarith

/-- Numerical value: `288 - S_charged - S_nuL = -17401/100`. -/
theorem closure_RHS_decimal :
    (288 : ℝ) - S_charged - S_nuL = -17401 / 100 := by
  rw [closure_RHS_eq_S_nuR]
  unfold S_nuR; norm_num

/-! ## Test: does Hypothesis A (mult = 1) force `y_R`? -/

/-- **Hypothesis A test.**  Under `mult = 1`, the closure equation
    `1 · (-log y_R) = -174.01` would force

      `−log y_R = −174.01`,

    i.e., `y_R = e^{174.01}`, a number > 10^{75} that is *grotesquely*
    incompatible with the empirical `y_R ≈ 3.27 × 10⁻⁵`.

    **Conclusion**: Hypothesis A is *strongly numerically rejected*
    by the closure equation (off by ~80 orders of magnitude).  Even
    if the J-restriction is taken at face value, it does not force
    a viable `y_R`.

    *Tier 1 — algebraic.* -/
theorem hypA_forces_unphysical_yR :
    closure_constraint multA (Real.exp (-(-17401/100))) := by
  unfold closure_constraint multA
  rw [closure_RHS_decimal]
  -- Show 1 * (-log (exp 17401/100)) = -17401/100
  have h : -Real.log (Real.exp (-(-17401/100))) = -17401/100 := by
    rw [Real.log_exp]; ring
  linarith

/-! ## Test: does Hypothesis B (mult = 6) force `y_R`? -/

/-- **Hypothesis B test.**  Under `mult = 6`, the closure equation
    `6 · (-log y_R) = -174.01` would force

      `−log y_R = −174.01/6 ≈ -29.0`,

    i.e., `y_R = e^{29.0} ≈ 4 × 10^{12}`, also wildly incompatible
    with `y_R ≈ 3.27 × 10⁻⁵`.

    **Conclusion**: Hypothesis B *also* fails to force a viable
    `y_R` from a one-mode J-restriction.  The reason is that the
    framework's existing 288 closure uses `S_νR` as a *3-generation
    sum with see-saw cancellation* — not as a single-mode
    `mult · (-log y_R)`.  The J-restriction over-simplifies. -/
theorem hypB_forces_unphysical_yR :
    closure_constraint multB (Real.exp (-(-17401/600))) := by
  unfold closure_constraint multB
  rw [closure_RHS_decimal]
  have h : -Real.log (Real.exp (-(-17401/600))) = -17401/600 := by
    rw [Real.log_exp]; ring
  linarith

/-- Numerical comparison: empirical `y_R ≈ 3.27 × 10⁻⁵` corresponds
    to `−log y_R ≈ 10.33`.  Neither Hypothesis-A's `−log y_R = 174.01`
    nor Hypothesis-B's `−log y_R = 29.0` is anywhere near that. -/
noncomputable def empirical_neg_log_yR : ℝ := 1033 / 100  -- 10.33

/-- **Tier 1 — the J-restriction does NOT force a viable `y_R`.**

    For any choice of multiplicity (Hypothesis A or B), the closure
    equation `mult · (-log y_R) = -174.01` produces a `y_R` that is
    incompatible with the empirical `y_R ≈ 3.27 × 10⁻⁵` by many
    orders of magnitude.  Specifically:

      * Hypothesis A: `−log y_R = -174.01` (off by ~184)
      * Hypothesis B: `−log y_R = -29.0`   (off by ~39)

    Both are *negative*, contradicting the trivial `y_R < 1` ⇒
    `−log y_R > 0` requirement of `negLogY_nonneg`.  Hence the
    J-restricted closure forces `y_R > 1`, an unphysically large
    Yukawa coupling. -/
theorem J_restriction_does_not_force_viable_yR :
    -- Hypothesis A's required y_R is much greater than 1
    (288 - S_charged - S_nuL) / (multA : ℝ) < 0 ∧
    -- Hypothesis B's required y_R is much greater than 1
    (288 - S_charged - S_nuL) / (multB : ℝ) < 0 := by
  rw [closure_RHS_decimal]
  unfold multA multB
  refine ⟨?_, ?_⟩
  · norm_num
  · norm_num

/-! ## The structural reason: see-saw cancellation lives in `S_νR`, NOT in `y_R^{-2s}`

The single-mode `mult · y_R^{-2s}` model misses the *see-saw*
correlation between Dirac and Majorana neutrinos, which is the
M_R-cancellation captured by `seesaw_product_independence`.  The
288 closure uses the *combined* `(S_νL + S_νR) = 10.61` in place
of `mult · (-log y_R)`, and that combination is what is determined
by the geometric mean of the Dirac neutrino masses.

So the J-restricted ζ_F(0; ν_R) is **not** the relevant quantity for
the 288 closure: the relevant quantity is `S_νL + S_νR`, which is a
*two-mode* combination from the type-I see-saw, and equals `10.61`
empirically. -/

/-- **Tier 1 — the load-bearing structural observation.**

    The closure value `S_νL + S_νR = 10.61` is what the framework's
    288 identity uses, *not* the single-mode `mult · (-log y_R)`.
    These are different objects.  -/
theorem closure_uses_combined_seesaw :
    S_nuL + S_nuR = 1061 / 100 := K_seesaw_decimal

/-- The framework's empirical `−log y_R ≈ 10.33` is *consistent* with
    the combined `(S_νL + S_νR) = 10.61` *if* one identifies them at
    multiplicity 1 — but that's Hypothesis A, which the discriminator
    rules out under standard NCG. -/
theorem empirical_consistent_with_combined :
    |empirical_neg_log_yR - (S_nuL + S_nuR)| < 1 / 2 := by
  unfold empirical_neg_log_yR
  rw [K_seesaw_decimal]
  rw [abs_sub_lt_iff]
  refine ⟨?_, ?_⟩ <;> norm_num

/-! ## Verdict-flavor lemmas (full verdict in `Verdict.lean`) -/

/-- **Tier 1 — summary of the J-restriction's failure to force `y_R`.**

    Three independent failures:
      (a) `ζ_F(0; ν_R) = mult ∈ {1, 6}`, neither is `8`.
      (b) The closure equation `mult · (-log y_R) = -174.01` forces
          a negative `−log y_R`, hence `y_R > 1`, unphysical.
      (c) The framework's actual closure uses the see-saw-corrected
          `(S_νL + S_νR) = 10.61`, *not* a single-mode formula.

    All three are Tier 1. -/
theorem J_restriction_failure_summary :
    -- (a) value at zero is multiplicity, neither is 8
    (multA ≠ target_eight) ∧ (multB ≠ target_eight) ∧
    -- (b) closure forces y_R > 1
    ((288 - S_charged - S_nuL) / (multA : ℝ) < 0) ∧
    ((288 - S_charged - S_nuL) / (multB : ℝ) < 0) ∧
    -- (c) framework's actual closure uses 10.61
    (S_nuL + S_nuR = 1061 / 100) := by
  refine ⟨multA_ne_eight, multB_ne_eight, ?_, ?_, K_seesaw_decimal⟩
  · rw [closure_RHS_decimal]; unfold multA; norm_num
  · rw [closure_RHS_decimal]; unfold multB; norm_num

end SpectralPhysics.ZetaFNuR
