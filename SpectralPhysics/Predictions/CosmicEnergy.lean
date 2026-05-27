/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Triad.SelfReferentialTriad
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Cosmic energy budget from the self-referential tolerance `τ = 1/(2+φ)`

The framework's cosmic energy fractions are identified with algebraic
combinations of the self-referential tolerance `τ = 1/(2+φ)` and the golden
ratio `φ`, per manuscript v1.0 Proposition `prop:omega-budget`
(`spectral-physics-latest.tex` lines 23627–23634):

  Ω_DM ≈ τ            ≈ 0.276   (measured 0.265 ± 0.007)
  Ω_b  ≈ τ²/φ         ≈ 0.047   (measured 0.050 ± 0.001)
  Ω_Λ  ≈ 1 − τ − τ²/φ ≈ 0.677   (measured 0.685 ± 0.007)

## Tier classification (manuscript v1.0, honest)

* **Tier 3 (model, NOT first-principles derivation).** `Ω_DM` and `Ω_b` are
  *identified* with `τ` and `τ²/φ` via the coherence-cutoff interpretation;
  the framework *models* the fractions, it does not derive them (manuscript
  line 23636–23642). The matches are striking (~1–3σ) but the derivation
  chain is shorter than the Tier-1/Tier-2 results.
* **`Ω_Λ` is a closure-RESIDUAL**, not an independent prediction: it is fixed
  by `Ω_tot = 1` given `Ω_DM + Ω_b` (manuscript line 23644–23650, Group-5
  audit fix). Reporting an "agreement %" for `Ω_Λ` is *not* the same kind of
  confirmation as for `Ω_DM`. (Tier 1 separately identifies `Λ = λ₁`, the
  cosmic-Laplacian spectral gap — that is the CC *mode identification*, a
  different claim from this fraction; see `results/CHAIN-RIGOR-LEDGER.md`.)

## History

This file previously encoded a *superseded* triad budget
(`Ω_DM = 1−3τ ≈ 0.171`, `Ω_DE = 2τ ≈ 0.553`); `0.553` was ~15σ from the
observed `0.685`. Rewritten 2026-05-26 to the manuscript v1.0 budget above
(which closes to `Ω_tot = 1` and matches observation to ~1–3σ).

## References

* Ben-Shalom, "Spectral Physics", v1.0 Prop. `prop:omega-budget`
  (`spectral-physics-latest.tex` §`sec:cosmic-budget`).
* `Triad/SelfReferentialTriad.lean` (`τ`, `φ`, `tau_closed_form`).
-/

noncomputable section

open Real

namespace SpectralPhysics.CosmicEnergy

/-- Dark-matter fraction: `Ω_DM = τ`. -/
def omega_DM : ℝ := τ

/-- Baryon fraction: `Ω_b = τ²/φ`. -/
def omega_b : ℝ := τ ^ 2 / φ

/-- Dark-energy fraction (closure-residual): `Ω_Λ = 1 − τ − τ²/φ`. -/
def omega_Lambda : ℝ := 1 - τ - τ ^ 2 / φ

/-- **Cosmic sum rule** (exact, by construction): the three fractions close
    to `Ω_tot = 1`.  This is *why* `Ω_Λ` is a residual, not an independent
    prediction. -/
theorem cosmic_sum_rule : omega_DM + omega_b + omega_Lambda = 1 := by
  unfold omega_DM omega_b omega_Lambda; ring

/-! ## √5 brackets (golden-ratio numerics) -/

private theorem sqrt5_lo : (2.236 : ℝ) < Real.sqrt 5 := by
  rw [show (2.236 : ℝ) = Real.sqrt (2.236 ^ 2) from
    (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

private theorem sqrt5_hi : Real.sqrt 5 < (2.237 : ℝ) := by
  rw [show (2.237 : ℝ) = Real.sqrt (2.237 ^ 2) from
    (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

private theorem phi_pos : (0 : ℝ) < φ := by
  show (0:ℝ) < (1 + Real.sqrt 5)/2
  have := Real.sqrt_nonneg 5; positivity

/-! ## Closed forms in `√5` -/

/-- `Ω_DM = (5 − √5)/10 ≈ 0.2764`. -/
theorem omega_DM_closed : omega_DM = (5 - Real.sqrt 5) / 10 := tau_closed_form

/-- `Ω_b = (√5 − 2)/5 ≈ 0.0472`. -/
theorem omega_b_closed : omega_b = (Real.sqrt 5 - 2) / 5 := by
  have hs : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hφ : φ = (1 + Real.sqrt 5) / 2 := rfl
  have h1 : (1 + Real.sqrt 5) ≠ 0 := by have := Real.sqrt_nonneg 5; positivity
  unfold omega_b
  rw [tau_closed_form, hφ]
  field_simp
  nlinarith [hs, Real.sqrt_nonneg 5]

/-- `Ω_Λ = (9 − √5)/10 ≈ 0.6764`. -/
theorem omega_Lambda_closed : omega_Lambda = (9 - Real.sqrt 5) / 10 := by
  have h := cosmic_sum_rule
  rw [omega_DM_closed, omega_b_closed] at h
  linarith

/-! ## Observational brackets -/

/-- `Ω_DM ≈ 0.276` (measured 0.265 ± 0.007). -/
theorem omega_DM_bracket : (0.276 : ℝ) < omega_DM ∧ omega_DM < 0.277 := by
  rw [omega_DM_closed]
  constructor <;> [linarith [sqrt5_hi]; linarith [sqrt5_lo]]

/-- `Ω_b ≈ 0.047` (measured 0.050 ± 0.001). -/
theorem omega_b_bracket : (0.047 : ℝ) < omega_b ∧ omega_b < 0.048 := by
  rw [omega_b_closed]
  constructor <;> [linarith [sqrt5_lo]; linarith [sqrt5_hi]]

/-- `Ω_Λ ≈ 0.676` (measured 0.685 ± 0.007); closure-residual. -/
theorem omega_Lambda_bracket : (0.676 : ℝ) < omega_Lambda ∧ omega_Lambda < 0.677 := by
  rw [omega_Lambda_closed]
  constructor <;> [linarith [sqrt5_hi]; linarith [sqrt5_lo]]

end SpectralPhysics.CosmicEnergy

end
