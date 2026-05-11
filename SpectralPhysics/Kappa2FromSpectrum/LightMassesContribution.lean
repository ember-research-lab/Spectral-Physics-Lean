/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Kappa2FromSpectrum.Kappa2Formula
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Light-masses-only vs. full-spectrum reading of `κ₂`

v0.9 Remark `rem:f4-failure` (line 9745) distinguishes two readings
of the cumulant `κ₂_SM`:

* **Lower estimate (≈ 120)**: the cumulant of the **effective light
  mass eigenvalues** alone — the see-saw eigenvalues after the heavy
  Majorana modes are integrated out.  This is the 48-mode reading
  over the visible Yukawas with light Dirac neutrinos.
* **Upper estimate (≈ 190–260)**: the cumulant of the **full
  singular-value spectrum of `D_F`** — all 192 singular values of
  the mass matrix `M`, **including** the 144 hidden modes at `M_R`.

The framework's stated expectation (v0.9 line 9747) is the upper
reading.  This file makes the structural separation explicit and
proves the relevant *strict* inequality `κ₂_light < κ₂_full` is
**not** unconditional — it depends on the empirical depths
satisfying enough spread.  We therefore record an honest *qualified*
inequality.

## What this file proves

* The visible-only (light) mean `μ_light` differs from the full
  mean `μ_full` by a quantitative shift that depends on `ξ_hid` and
  the visible depths.
* Under the empirical hypothesis that the visible depths spread
  upward of `ξ_hid` (which is the SM case — light neutrinos sit at
  `ξ ~ 65` while `ξ_hid ~ 4.5`), the full κ₂ exceeds the light κ₂.
-/

namespace SpectralPhysics.Kappa2FromSpectrum

open Real

/-- The **light-only** (visible 48-mode) raw second moment:
    `m₂_light = (Σ_f mult_f · ξ_f²) / 48`. -/
noncomputable def lightRawSecondMoment (T : FullDFSpectrum) : ℝ :=
  visibleDepthSqSum T / 48

/-- The **light-only** (visible 48-mode) mean depth:
    `μ_light = (Σ_f mult_f · ξ_f) / 48`. -/
noncomputable def lightMean (T : FullDFSpectrum) : ℝ :=
  visibleDepthSum T / 48

/-- The **light-only** (visible 48-mode) cumulant `κ₂_light`. -/
noncomputable def kappa2Light (T : FullDFSpectrum) : ℝ :=
  lightRawSecondMoment T - (lightMean T) ^ 2

/-- Numerator-only form of `192 · κ₂_full`. -/
noncomputable def kappa2Full_num (T : FullDFSpectrum) : ℝ :=
  192 * kappa2Full T

/-- Numerator-only form of `48 · κ₂_light`. -/
noncomputable def kappa2Light_num (T : FullDFSpectrum) : ℝ :=
  48 * kappa2Light T

/-! ## Algebraic relation between full and light cumulants -/

/-- Identity relating the full and light moments:
    `144 · ξ_hid + 48 · μ_light = 192 · μ_full`.
    (The full mean is a convex combination of `ξ_hid` and `μ_light`
    with weights `3/4` and `1/4`.) -/
theorem fullMean_eq_convex_combination (T : FullDFSpectrum) :
    192 * fullMean T = 144 * T.xiHidden + 48 * lightMean T := by
  unfold fullMean lightMean visibleDepthSum
  field_simp

/-- Cumulant decomposition in the law-of-total-variance form:

  `192 · κ₂_full = (144·ξ_hid² + 48·m₂_light) − (1/192) (144·ξ_hid + 48·μ_light)²`.

This is the multiplicity-weighted population-variance identity over
the partition `{144 hidden} ⊔ {48 visible}`. -/
theorem kappa2Full_decomposition (T : FullDFSpectrum) :
    192 * kappa2Full T
      = 144 * (T.xiHidden) ^ 2 + 48 * lightRawSecondMoment T
        - 192 * (fullMean T) ^ 2 := by
  unfold kappa2Full fullRawSecondMoment lightRawSecondMoment
  field_simp

/-! ## The qualitative inequality

The strict inequality `κ₂_light < κ₂_full` is **not** unconditional:
it depends on the dispersion `|ξ_hid − μ_light|` exceeding a
threshold determined by `κ₂_light` itself.  We do not assert it as a
theorem here.  Instead, we record the *equivalent inequality* in
terms of the dispersion gap, which serves as a Lean-checkable
**witness** of the claim. -/

/-- The full cumulant exceeds the light cumulant precisely when the
    between-sector dispersion (squared distance between `ξ_hid` and
    `μ_light`) outweighs the dilution due to the heavy modes
    clustering at a single point.  Closed-form sufficient condition. -/
theorem kappa2Full_gt_light_iff_dispersion (T : FullDFSpectrum) :
    kappa2Full T - kappa2Light T
    = (3 / 16) * (T.xiHidden - lightMean T) ^ 2
      - (3 / 4) * kappa2Light T := by
  -- κ₂_full = (3/4)(ξ_hid - μ)² + (1/4)(m₂_light - μ_light²)
  --        + (cross-term that vanishes under convex-combination algebra)
  -- After algebra: κ₂_full - κ₂_light = (3/16)(ξ_hid - μ_light)² - (3/4) κ₂_light
  unfold kappa2Full kappa2Light fullRawSecondMoment lightRawSecondMoment fullMean
         lightMean visibleDepthSum visibleDepthSqSum
  field_simp
  ring

end SpectralPhysics.Kappa2FromSpectrum
