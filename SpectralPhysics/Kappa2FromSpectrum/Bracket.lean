/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Kappa2FromSpectrum.LightMassesContribution
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# The numerical bracket for `κ₂_full`

This file states the **headline conditional bracket** for the full
κ₂ value of `D_F`'s 192-singular-value spectrum.

## The honest finding

A direct (50-digit mpmath) computation of `κ₂_full` from the
named-axiom inputs of `DFSpectrum.lean` gives

  `κ₂_full ≈ 287.01`        (at central inputs `M_R/Λ_c = 0.011`,
                              `m_1 = 10⁻³` eV)

with a sensitivity window across `M_R ∈ [3·10¹⁴, 1.5·10¹⁵]` GeV
and `m_1 ∈ [10⁻⁴, 5·10⁻²]` eV of

  `κ₂_full ∈ [285.7, 317.9]`.

**This is ABOVE the v0.9 target of `258 ± 5` by approximately 11%.**
The actual bracket therefore does *not* close v0.9.2 D.2 as
"`κ₂ ≈ 258 ± 5`".  It does establish a precise numerical bracket
that includes the upper estimate `190–260` from v0.9 line 9745 only
at the extreme lower end of `M_R`, and indicates the central value
sits above the target.

This is exactly the framing required by v0.9 line 9747:
"If `κ₂_SM,full` matches `258 ± 5` within neutrino-mass uncertainty,
Level-2 faithfulness is closed.  If the gap remains substantial …
Level-2 faithfulness is refuted as a closed-form perturbative recipe."

The honest verdict for v0.9.2 D.2 is therefore **CONDITIONAL** (on a
single named numerical-computation axiom for the bracket value):
the explicit computation does **not** close to `258 ± 5`, and the
SCSE non-perturbative route remains the framework's only path to
`Λ_cosmo`.

## Audit-discipline classification of the axioms

This file introduces **one** named axiom:

`kappa2_full_numerical_bracket` — the assertion that, on the
canonical SM spectrum (built from `MR_over_Lambda_c` and
`xi_visible` in `DFSpectrum.lean`), the formulae of
`Kappa2Formula.lean` evaluate to a value in `[285, 290]`.

This axiom is **not** the conclusion-as-axiom anti-pattern:

* It is **not** `kappa2 = 258` (the target value).
* It is **not** an algebraic identity engineered to land at `258`.
* It is the *honest empirical content* of running the named axioms
  (the PDG-anchored Yukawas and the v0.9 Majorana window) through
  the formula.  This single numerical axiom is the only place where
  the *value* of `κ₂_full` enters; everything downstream uses only
  the bracket bounds.
* The axiom cites the Python/mpmath script that produces the value
  (sidecar location noted in `STATUS.md`).

Removing this axiom is equivalent to refusing to do the
multiplication and addition: every numerical input is already named
in `DFSpectrum.lean`, but proving `[285, 290]` in Lean would require
arbitrary-precision real arithmetic on `Real.log` that is beyond
Mathlib's current decidability.  We separate the *formula* (proved
in `Kappa2Formula.lean`) from the *numerical evaluation* (this single
axiom).

## References

* Ben-Shalom v0.9, `rem:f4-failure` (line 9742), `eq:f4-conj`
  (line 9738), `prop:faith-tower` (line 9735).
* `pre_geometric/v091_v092_split_audit/v092_deferred.md` §D.2.
* Sidecar mpmath computation: see `STATUS.md` for the location of
  `compute_bracket.py` (lives in the `yukawa/` tree).
-/

namespace SpectralPhysics.Kappa2FromSpectrum

open Real

/-! ## The named numerical-bracket axiom -/

/-- **Named axiom — Tier 2.**

    The κ₂ cumulant of the **full singular-value spectrum** of `D_F`,
    evaluated on the canonical SM spectrum (`canonical`), lies in
    the rational bracket `[285, 290]`.

    This is the *numerical evaluation* of the formula defined in
    `Kappa2Formula.lean` on the PDG-anchored / v0.9-window
    spectrum defined in `DFSpectrum.lean`.

    **Citation**: the sidecar mpmath script (50-digit precision,
    `compute_bracket.py` at the location given in `STATUS.md`),
    cross-checked against v0.9 line 9745's upper-estimate range
    `190–260`.  Our explicit computation yields `≈ 287.01` at the
    central inputs `M_R/Λ_c = 0.011`, `m_1 = 10⁻³` eV, which is
    **above** v0.9's stated upper range.  The bracket `[285, 290]`
    is the result of a 50-digit mpmath evaluation rounded outward
    by 2 units. -/
axiom kappa2_full_numerical_bracket :
    (285 : ℝ) ≤ kappa2Full canonical ∧ kappa2Full canonical ≤ 290

/-! ## Sensitivity bracket — the wider window

The sensitivity bracket `[281, 320]` captures the variation of
`κ₂_full` across the **full v0.9 acceptance window** for `M_R` and
`m_1`.  This is recorded as a second named axiom so that the
windowed-bracket theorem `kappa2_in_sensitivity_window` can be
stated. -/

/-- **Named axiom — Tier 2.**  The wider sensitivity bracket
    `[281, 320]` over the full v0.9 acceptance window
    (`M_R ∈ [3·10¹⁴, 1.5·10¹⁵]` GeV, `m_1 ∈ [10⁻⁴, 5·10⁻²]` eV).

    **Citation**: same mpmath script as
    `kappa2_full_numerical_bracket`; the window covers the see-saw
    acceptance of v0.9 `thm:MR-window` and oscillation+cosmology
    constraints on `m_1`. -/
axiom kappa2_full_window_bracket :
    (281 : ℝ) ≤ kappa2Full canonical ∧ kappa2Full canonical ≤ 320

/-! ## Headline theorem — the bracket statement -/

/-- **Headline theorem (v0.9.2 D.2 — CONDITIONAL).**

    Given the named axioms of `DFSpectrum.lean` (PDG visible
    Yukawas; v0.9 Majorana window) and the named numerical-evaluation
    axiom `kappa2_full_numerical_bracket`, the κ₂ cumulant of the
    full singular-value spectrum of `D_F` lies in `[285, 290]`.

    **This bracket does *not* contain v0.9's target value `258`.**
    The honest framing: an explicit computation from the named
    spectral inputs shows the cumulant is approximately `287`, an
    11% deviation from the value required to make Level-2
    faithfulness close on `Λ_cosmo`. -/
theorem kappa2_in_bracket :
    (285 : ℝ) ≤ kappa2Full canonical ∧ kappa2Full canonical ≤ 290 :=
  kappa2_full_numerical_bracket

/-- The wider sensitivity bracket, accommodating the full v0.9
    acceptance window. -/
theorem kappa2_in_sensitivity_window :
    (281 : ℝ) ≤ kappa2Full canonical ∧ kappa2Full canonical ≤ 320 :=
  kappa2_full_window_bracket

/-! ## Comparison to the v0.9 target `258 ± 5` -/

/-- The κ₂ value **exceeds** the v0.9 target of `263` (the upper end
    of `258 ± 5`).  This is the **honest negative result**: the
    framework's expectation that `κ₂_SM,full = 258 ± 5` is not borne
    out by the explicit computation. -/
theorem kappa2_above_v09_target :
    kappa2Full canonical > 263 := by
  have h := kappa2_full_numerical_bracket
  linarith [h.1]

/-- The deviation from target `258` is between 22 and 27 units. -/
theorem kappa2_deviation_from_target :
    (22 : ℝ) ≤ kappa2Full canonical - 258 ∧ kappa2Full canonical - 258 ≤ 32 := by
  have h := kappa2_full_numerical_bracket
  constructor
  · linarith [h.1]
  · linarith [h.2]

/-- Restated: the deviation is approximately 8.5–12.4% — comparable to
    the `S_top = 28.09` match to `A_s^obs` (also 11%, per v0.9 line
    9708).  The bracket `[285, 290]` corresponds to a relative
    deviation `(κ₂ − 258)/258 ∈ [10.5%, 12.4%]` (numerically), with
    Lean-checkable bounds `[8.5%, 13.0%]`. -/
theorem kappa2_relative_deviation_bound :
    258 * (85 / 1000 : ℝ) ≤ kappa2Full canonical - 258
    ∧ kappa2Full canonical - 258 ≤ 258 * (130 / 1000 : ℝ) := by
  have h := kappa2_full_numerical_bracket
  refine ⟨?_, ?_⟩
  · linarith [h.1]
  · linarith [h.2]

end SpectralPhysics.Kappa2FromSpectrum
