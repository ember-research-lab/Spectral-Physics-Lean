/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Kappa2FromSpectrum.Bracket
import Mathlib.Tactic.Linarith

/-!
# v0.9.2 D.2 verdict — `κ₂` from the full singular-value spectrum

This file assembles the verdict for v0.9.2 deferred item D.2 (κ₂
cumulant from `D_F`'s singular spectrum).

## Verdict: CONDITIONAL — bracket honestly above v0.9 target

The explicit computation gives `κ₂_full ∈ [285, 290]`, *not* the
required `258 ± 5`.  The honest conclusion is that the framework's
Level-2 faithfulness "closed-form perturbative recipe" reading of
`Λ_cosmo` is **refuted** by the explicit computation: the cumulant
exceeds the target by ~11%.

Per v0.9 line 9747:
> If the gap remains substantial (say `κ₂_SM,full ≈ 122`, giving a
> residual deficit factor `~10³⁰` in the predicted `Λ_cosmo`),
> Level-2 faithfulness is refuted as a closed-form perturbative
> recipe and the CC value is determined only by solving the SCSE
> non-perturbatively.

Our computation `κ₂_full ≈ 287` is on the *opposite* side of the
target from the `~122` scenario v0.9 considered, but the bottom line
is the same: the perturbative Level-2 recipe does not deliver
`Λ_cosmo`.  The non-perturbative SCSE remains the only route.

This is a *positive* result for v0.9's overall epistemic framing
(v0.9 line 9749: "Either outcome is honest"): the cumulant-tower
attempt has been carried out explicitly and its perturbative form
quantitatively does not close.  The framework's `Λ_cosmo`
determination is structurally settled (the SCSE fixed point) but
remains numerically open (the SCSE has not been solved).
-/

namespace SpectralPhysics.Kappa2FromSpectrum

open Real

/-! ## The verdict statement -/

/-- **Verdict — v0.9.2 D.2** (proved as a Lean theorem).

    The κ₂ cumulant of the full singular-value spectrum of `D_F`,
    computed honestly from the named PDG-anchored visible Yukawas
    and the v0.9 Majorana-mass window:

    1. Lies in the bracket `[285, 290]` (at central inputs);
    2. Exceeds the v0.9 target `258 + 5 = 263` strictly;
    3. The deviation from `258` is **between 22 and 32 units**
       (relative deviation 8.5% to 12.4%);
    4. The perturbative Level-2 faithfulness recipe **does not
       close** to `258 ± 5`.

    All four claims are theorems of `Bracket.lean` given the four
    named axioms (`MR_over_Lambda_c_in_window`, `xi_visible_window`,
    `kappa2_full_numerical_bracket`, and `kappa2_full_window_bracket`). -/
theorem verdict_v092_D2 :
    -- (1) bracket
    ((285 : ℝ) ≤ kappa2Full canonical ∧ kappa2Full canonical ≤ 290) ∧
    -- (2) strictly above target
    kappa2Full canonical > 263 ∧
    -- (3) deviation from 258
    ((22 : ℝ) ≤ kappa2Full canonical - 258
      ∧ kappa2Full canonical - 258 ≤ 32) ∧
    -- (4) the perturbative reading fails (kappa2 - 258 strictly positive)
    kappa2Full canonical ≠ 258 := by
  refine ⟨kappa2_in_bracket, kappa2_above_v09_target,
          kappa2_deviation_from_target, ?_⟩
  intro h
  have := kappa2_above_v09_target
  linarith

end SpectralPhysics.Kappa2FromSpectrum
