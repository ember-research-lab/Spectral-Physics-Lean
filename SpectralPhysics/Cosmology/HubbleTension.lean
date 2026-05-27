/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Hubble tension as a scale-dependent measurement effect (PARTIAL mechanism)

Manuscript v1.0 Theorem `thm:hubble-tension` (`spectral-physics-latest.tex`
lines 24589–24606): the early-universe (CMB) vs late-universe (local) `H₀`
discrepancy receives a scale-dependent measurement contribution

  α = g · (r_s / L_H) ≈ 0.5 · (150 Mpc / 4300 Mpc) ≈ 0.017,

with `g = 0.5` from a Kaiser-multipole projection of redshift-space peculiar
velocities. This accounts for `≈ 20%` of the SH0ES–Planck tension, reducing
`~5σ → ~4σ`. **`≈ 80%` remains unexplained** — additional physics (early sound
horizon or late-time ρ_DE(z)) is needed.

## Tier classification — **Tier 3 (model, PARTIAL), honest**

* `g = 0.5` is a **fit choice** (Kaiser-multipole with radial weight
  `f_r ≈ 0.7`, line-of-sight `~0.5`, transverse `~0.84`), NOT a derived
  parameter (manuscript line 24600, Group-5 audit fix demoting from Tier 2).
* This is a **candidate mechanism for ~20%** of the tension, **NOT a
  resolution**. The framework does not resolve the Hubble tension.
* `r_s ≈ 150 Mpc` (sound horizon) and `L_H ≈ 4300 Mpc` (Hubble length `c/H₀`)
  are standard cosmological inputs; the `H₀` values are SH0ES/Planck data.

The theorems below verify the *arithmetic* of the manuscript's claim (the
`≈ 0.017` magnitude, the `~20%` fraction, the `5σ → 4σ` reduction). They do
NOT validate the geometric `g`-mechanism, which is the Tier-3 fit content.
See `results/CHAIN-RIGOR-LEDGER.md`.
-/

noncomputable section

namespace SpectralPhysics.Cosmology

/-- Kaiser-multipole geometric projection factor (FIT choice, `f_r ≈ 0.7`). -/
def hubbleG : ℝ := 1 / 2

/-- Sound horizon `r_s ≈ 150 Mpc`. -/
def soundHorizonMpc : ℝ := 150

/-- Hubble length `L_H = c/H₀ ≈ 4300 Mpc`. -/
def hubbleLengthMpc : ℝ := 4300

/-- The scale-dependent measurement contribution `α = g · r_s / L_H`. -/
def alphaScaleEffect : ℝ := hubbleG * (soundHorizonMpc / hubbleLengthMpc)

/-- SH0ES (late-universe / local) `H₀ ≈ 73 km/s/Mpc`. -/
def H0_late : ℝ := 73
/-- Planck (early-universe / CMB) `H₀ ≈ 67 km/s/Mpc`. -/
def H0_early : ℝ := 67
/-- Reference `H₀ ≈ 70` for the fractional discrepancy. -/
def H0_ref : ℝ := 70

/-- Fractional SH0ES–Planck `H₀` discrepancy `(H_late − H_early)/H_ref ≈ 0.086`. -/
def H0_fracDiscrepancy : ℝ := (H0_late - H0_early) / H0_ref

/-! ## Arithmetic of the manuscript claim (T1) -/

/-- `α = 3/172 ≈ 0.01744`. -/
theorem alpha_closed : alphaScaleEffect = 3 / 172 := by
  unfold alphaScaleEffect hubbleG soundHorizonMpc hubbleLengthMpc; norm_num

/-- `α ≈ 0.017`. -/
theorem alpha_bracket : (0.0174 : ℝ) < alphaScaleEffect ∧ alphaScaleEffect < 0.0175 := by
  rw [alpha_closed]; constructor <;> norm_num

/-- Fractional discrepancy `= 3/35 ≈ 0.0857`. -/
theorem fracDiscrepancy_closed : H0_fracDiscrepancy = 3 / 35 := by
  unfold H0_fracDiscrepancy H0_late H0_early H0_ref; norm_num

/-- The scale-effect-to-discrepancy ratio `α / Δ = 35/172 ≈ 0.2035`. -/
theorem fraction_explained_eq : alphaScaleEffect / H0_fracDiscrepancy = 35 / 172 := by
  rw [alpha_closed, fracDiscrepancy_closed]; norm_num

/-- **Accounts for ≈ 20%.** The scale-dependent effect explains between 20% and
    21% of the fractional `H₀` discrepancy. -/
theorem accounts_for_about_20pct :
    (0.20 : ℝ) < alphaScaleEffect / H0_fracDiscrepancy ∧
    alphaScaleEffect / H0_fracDiscrepancy < 0.21 := by
  rw [fraction_explained_eq]; constructor <;> norm_num

/-- **`~5σ → ~4σ`.** Removing the `≈ 20%` scale-effect fraction from a `5σ` raw
    tension leaves a residual in `(3.9, 4.1)σ` — the manuscript's headline. -/
theorem tension_reduced_to_about_4sigma :
    (3.9 : ℝ) < (1 - alphaScaleEffect / H0_fracDiscrepancy) * 5 ∧
    (1 - alphaScaleEffect / H0_fracDiscrepancy) * 5 < 4.1 := by
  rw [fraction_explained_eq]; constructor <;> norm_num

/-- **PARTIAL, not a resolution.** The mechanism explains well under a third of
    the tension; `≈ 80%` remains and requires additional physics. -/
theorem partial_mechanism_only :
    alphaScaleEffect / H0_fracDiscrepancy < 1 / 3 := by
  rw [fraction_explained_eq]; norm_num

end SpectralPhysics.Cosmology

end
