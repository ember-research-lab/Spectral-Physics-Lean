/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Triad.SelfReferentialTriad
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The SAGF Trace-Sector Dispersion Symbol  σ_tr(ξ)

The Spectral-Action Gradient Flow (SAGF) of the metric, after York
decomposition, projects onto the conformal-trace mode.  Linearising
around a fixed background and Fourier-transforming, the kinetic
operator on the trace sector is

  σ_tr(ξ)  =  c₁ · f₂ · Λ² · ξ²  −  6 · f₀ · α_eff · ξ⁴ ,        (*)

where

* `c₁ = 1/2`   (Route B, heat-kernel / Lichnerowicz–York; see
  `pre_geometric/c1_and_5sector/verdict.md`),
* `f₀ = τ`   (Level-0 faithfulness, framework primitive),
* `f₂ = 48 e⁶`   (Level-1 faithfulness, framework primitive),
* `α_eff`   (positive ε² regulator coefficient).

The crossover scale ξ_cross is the *positive* root of `σ_tr(ξ) = 0`
above ξ = 0, given by

  ξ_cross²  =  c₁ · f₂ · Λ²  /  (6 · f₀ · α_eff) .

Below ξ_cross, σ_tr(ξ) > 0 and the trace mode is anti-diffusive
(tachyonic in the Wick-rotated sense).  Above ξ_cross, σ_tr(ξ) < 0
and the higher-curvature regulator dominates.

## Main results

* `sigmaTr` : the dispersion symbol, defined as a function of `ξ`.
* `xiCrossSq` : the crossover momentum squared.
* `sigmaTr_at_xiCross` : `σ_tr(ξ_cross) = 0`.
* `sigmaTr_pos_below_crossover` : for `0 < ξ < ξ_cross`, `σ_tr > 0`.
* `sigmaTr_neg_above_crossover` : for `ξ > ξ_cross`, `σ_tr < 0`.
* `sigmaTr_zero_at_zero` : `σ_tr(0) = 0`.
* `xiCross_transPlanckian` : with `c₁ = 1/2`, `f₂/f₀ ≫ 1`, the
  crossover is parametrically larger than `Λ` (Route B verdict).

## References

* Whitt, B. (1984). *Phys. Lett. B* 145, 176.
* De Felice, A. & Tsujikawa, S. (2010). *Living Rev. Relativity* 13, 3.
* Ben-Shalom (2026). `pre_geometric/c1_and_5sector/verdict.md`.
* Codello, A. & Percacci, R. (2009). *Class. Quantum Grav.* 26, 175005.
-/

noncomputable section

open Real

namespace SpectralPhysics.Cosmology

/-! ## Section 1: Framework primitives -/

/-- **Route B value of `c₁`.**  From the heat-kernel /
Lichnerowicz–York calculation, the trace-sector projection coefficient
of the linearised SAGF kinetic operator is `c₁ = (n−2)/n = 1/2` in
`n = 4`.  This is *not* derived inside the v0.9 closure principles
(see `c1_and_5sector/verdict.md`); it is imported as a textbook
primitive of standard f(R)/heat-kernel machinery. -/
def c1RouteB : ℝ := 1 / 2

/-- `c₁ > 0` (the conformal-mode-problem sign). -/
theorem c1RouteB_pos : 0 < c1RouteB := by
  unfold c1RouteB; norm_num

/-- `f₀ = τ`, the framework's Level-0 faithfulness primitive
(inverse of the spectral gap of the triad Laplacian on `O–S–R`). -/
def f0 : ℝ := τ

/-- `τ > 0`, so `f₀ > 0`. -/
theorem f0_pos : 0 < f0 := by
  unfold f0
  -- τ = 1 / (2 + φ); 2 + φ > 0 since φ > 0
  unfold τ
  have hφ : 0 < φ := by unfold φ; positivity
  have : 0 < 2 + φ := by linarith
  exact div_pos one_pos this

/-- `f₂ = 48 · e⁶`, the framework's Level-1 faithfulness primitive
(exponential of per-mode log-Yukawa, Connes–Marcolli normalisation). -/
def f2 : ℝ := 48 * Real.exp 6

theorem f2_pos : 0 < f2 := by
  unfold f2
  exact mul_pos (by norm_num) (Real.exp_pos _)

/-- A canonical positive normalisation of `α_eff` (the higher-curvature
regulator coefficient).  In v0.9 the often-quoted value is
`α_eff = 1/120`; here we expose it as a *positive* parameter so
downstream theorems may quantify over it. -/
def alphaEff : ℝ := 1 / 120

theorem alphaEff_pos : 0 < alphaEff := by
  unfold alphaEff; norm_num

/-! ## Section 2: The dispersion symbol -/

/-- **The SAGF trace-sector dispersion symbol.**

  σ_tr(Λ; ξ) = c₁ · f₂ · Λ² · ξ² − 6 · f₀ · α_eff · ξ⁴ .

We expose `Λ` (the spectral cutoff) as an explicit argument because
the σ_tr-positive regime is `Λ`-dependent. -/
def sigmaTr (Λ ξ : ℝ) : ℝ :=
  c1RouteB * f2 * Λ^2 * ξ^2 - 6 * f0 * alphaEff * ξ^4

/-- **Vanishing at zero momentum.** -/
theorem sigmaTr_zero_at_zero (Λ : ℝ) : sigmaTr Λ 0 = 0 := by
  unfold sigmaTr; ring

/-- **The crossover momentum squared.**

  ξ_cross²  =  c₁ · f₂ · Λ²  /  (6 · f₀ · α_eff) .

This is the unique positive root of `σ_tr(Λ; ξ) = 0` in `ξ²` away
from `ξ² = 0`. -/
def xiCrossSq (Λ : ℝ) : ℝ :=
  c1RouteB * f2 * Λ^2 / (6 * f0 * alphaEff)

/-- For `Λ > 0`, the crossover scale squared is positive. -/
theorem xiCrossSq_pos (Λ : ℝ) (hΛ : 0 < Λ) : 0 < xiCrossSq Λ := by
  unfold xiCrossSq
  have hnum : 0 < c1RouteB * f2 * Λ^2 :=
    mul_pos (mul_pos c1RouteB_pos f2_pos) (by positivity)
  have hden : 0 < 6 * f0 * alphaEff :=
    mul_pos (mul_pos (by norm_num : (0:ℝ) < 6) f0_pos) alphaEff_pos
  exact div_pos hnum hden

/-- **Vanishing at the crossover.**

If `ξ² = ξ_cross²`, then `σ_tr(Λ; ξ) = 0`. -/
theorem sigmaTr_at_xiCross (Λ ξ : ℝ) (hΛ : 0 < Λ)
    (hξ : ξ^2 = xiCrossSq Λ) : sigmaTr Λ ξ = 0 := by
  unfold sigmaTr
  have hden_pos : 0 < 6 * f0 * alphaEff :=
    mul_pos (mul_pos (by norm_num : (0:ℝ) < 6) f0_pos) alphaEff_pos
  have hden_ne : (6 * f0 * alphaEff) ≠ 0 := ne_of_gt hden_pos
  -- Multiply hξ through: 6 f₀ α_eff · ξ² = c₁ f₂ Λ²
  have hsubst : 6 * f0 * alphaEff * ξ^2 = c1RouteB * f2 * Λ^2 := by
    rw [hξ]
    unfold xiCrossSq
    have hf0_ne : f0 ≠ 0 := ne_of_gt f0_pos
    have hα_ne : alphaEff ≠ 0 := ne_of_gt alphaEff_pos
    field_simp
  -- σ_tr = c₁ f₂ Λ² ξ² - 6 f₀ α_eff ξ⁴
  --     = c₁ f₂ Λ² ξ² - (6 f₀ α_eff ξ²) · ξ²
  --     = c₁ f₂ Λ² ξ² - (c₁ f₂ Λ²) · ξ²
  --     = 0
  have : c1RouteB * f2 * Λ^2 * ξ^2 - 6 * f0 * alphaEff * ξ^4
       = c1RouteB * f2 * Λ^2 * ξ^2 - (6 * f0 * alphaEff * ξ^2) * ξ^2 := by ring
  rw [this, hsubst]; ring

/-- **Anti-diffusivity below the crossover.**

For `0 < ξ² < ξ_cross²`, the trace mode is anti-diffusive:
`σ_tr(Λ; ξ) > 0`. -/
theorem sigmaTr_pos_below_crossover (Λ ξ : ℝ) (_hΛ : 0 < Λ)
    (hξ_pos : 0 < ξ^2) (hξ_below : ξ^2 < xiCrossSq Λ) :
    0 < sigmaTr Λ ξ := by
  unfold sigmaTr
  -- σ_tr = ξ² · (c₁ f₂ Λ² − 6 f₀ α_eff · ξ²)
  have hden_pos : 0 < 6 * f0 * alphaEff :=
    mul_pos (mul_pos (by norm_num : (0:ℝ) < 6) f0_pos) alphaEff_pos
  -- Show c₁ f₂ Λ² - 6 f₀ α_eff · ξ² > 0
  have h_inner : 0 < c1RouteB * f2 * Λ^2 - 6 * f0 * alphaEff * ξ^2 := by
    -- ξ² < c₁ f₂ Λ² / (6 f₀ α_eff) ⇒ ξ² · (6 f₀ α_eff) < c₁ f₂ Λ²
    have hkey : ξ^2 * (6 * f0 * alphaEff) < c1RouteB * f2 * Λ^2 := by
      unfold xiCrossSq at hξ_below
      exact (lt_div_iff₀ hden_pos).mp hξ_below
    linarith
  have h_factor : c1RouteB * f2 * Λ^2 * ξ^2 - 6 * f0 * alphaEff * ξ^4 =
      ξ^2 * (c1RouteB * f2 * Λ^2 - 6 * f0 * alphaEff * ξ^2) := by ring
  rw [h_factor]
  exact mul_pos hξ_pos h_inner

/-- **Diffusivity above the crossover.**

For `ξ² > ξ_cross²`, the higher-curvature regulator dominates:
`σ_tr(Λ; ξ) < 0`. -/
theorem sigmaTr_neg_above_crossover (Λ ξ : ℝ) (hΛ : 0 < Λ)
    (hξ_above : xiCrossSq Λ < ξ^2) :
    sigmaTr Λ ξ < 0 := by
  unfold sigmaTr
  have hden_pos : 0 < 6 * f0 * alphaEff :=
    mul_pos (mul_pos (by norm_num : (0:ℝ) < 6) f0_pos) alphaEff_pos
  -- ξ² > xiCrossSq > 0 ⇒ ξ² > 0
  have hξ_pos : 0 < ξ^2 := lt_trans (xiCrossSq_pos Λ hΛ) hξ_above
  have h_inner : c1RouteB * f2 * Λ^2 - 6 * f0 * alphaEff * ξ^2 < 0 := by
    have h2 : c1RouteB * f2 * Λ^2 < ξ^2 * (6 * f0 * alphaEff) := by
      unfold xiCrossSq at hξ_above
      exact (div_lt_iff₀ hden_pos).mp hξ_above
    linarith
  have h_factor : c1RouteB * f2 * Λ^2 * ξ^2 - 6 * f0 * alphaEff * ξ^4 =
      ξ^2 * (c1RouteB * f2 * Λ^2 - 6 * f0 * alphaEff * ξ^2) := by ring
  rw [h_factor]
  exact mul_neg_of_pos_of_neg hξ_pos h_inner

/-! ## Section 3: The crossover is trans-Planckian on Route B

With `c₁ = 1/2`, `f₂ = 48 e⁶`, `f₀ = τ ≈ 0.276`, `α_eff = 1/120`,

  ξ_cross² / Λ²  =  c₁ · f₂ / (6 · f₀ · α_eff)
                  =  (1/2) · (48 e⁶) / (6 · τ · (1/120))
                  =  4 · 120 · e⁶ / (6 · τ)
                  =  80 · e⁶ / τ
                  ≈  80 · 403.43 / 0.276
                  ≈  117 000

so `ξ_cross ≈ 342 · Λ`, i.e. between two and three orders of magnitude
above the spectral cutoff `Λ`.  This *confirms* the verdict in
`c1_and_5sector/verdict.md`: the trace mode is anti-diffusive across
the entire physical IR. -/

/-- **Trans-Planckian crossover.**

The crossover momentum squared exceeds `100 · Λ²` whenever `Λ > 0`.
This realises the verdict that ξ_cross is parametrically above the
spectral cutoff for Route B's `c₁ = 1/2`. -/
theorem xiCrossSq_transPlanckian (Λ : ℝ) (hΛ : 0 < Λ) :
    100 * Λ^2 < xiCrossSq Λ := by
  -- xiCrossSq Λ = (1/2) · 48 e⁶ · Λ² / (6 · τ · (1/120))
  --             = 24 e⁶ Λ² / (τ/20) = 480 e⁶ Λ² / τ
  -- We just need 480 e⁶ / τ > 100, i.e. e⁶ / τ > 100/480 = 5/24.
  -- e⁶ > 400 and τ < 1, so e⁶/τ > 400 ≫ 5/24.
  unfold xiCrossSq c1RouteB f2 f0 alphaEff
  -- (1/2 * (48 * exp 6) * Λ^2) / (6 * τ * (1/120))
  have hτ_pos : 0 < τ := by
    unfold τ
    have hφ : 0 < φ := by unfold φ; positivity
    exact div_pos one_pos (by linarith)
  have hτ_lt_one : τ < 1 := by
    unfold τ
    have hφ : 0 < φ := by unfold φ; positivity
    have : 1 < 2 + φ := by linarith
    exact (div_lt_one (by linarith)).mpr this
  have hexp6 : (400 : ℝ) < Real.exp 6 := by
    -- exp 6 > exp(ln 400) iff 6 > ln 400; ln 400 < 6 since e^6 > 400
    have h1 : Real.exp 6 = Real.exp 6 := rfl
    -- Use exp_lt iff via known bounds: e ≥ 2.718, so e^6 ≥ 2.7^6 = 387.42, but we need > 400.
    -- Use e > 2.71, so e^6 > 2.71^6.
    -- A cleaner route: exp(6) > 1 + 6 + 18 + 36 + 54 + 64.8 + 64.8 + ... use Taylor lower bound
    -- 1 + 6 + 36/2 + 216/6 + 1296/24 + 7776/120 + 46656/720
    -- = 1 + 6 + 18 + 36 + 54 + 64.8 + 64.8 = 244.6 (still < 400)
    -- Better: Real.add_one_lt_exp or use Real.exp_one_lt_d9 / Real.exp_one_gt_d9.
    -- exp_one > 2.7182818283 (mathlib lemma). 2.7182818283^6 > 400.
    have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have he6 : Real.exp 6 = (Real.exp 1)^6 := by
      have h6eq : (6 : ℝ) = (6 : ℕ) * 1 := by norm_num
      rw [h6eq, Real.exp_nat_mul]
    rw [he6]
    have hpos : (0 : ℝ) ≤ 2.7182818283 := by norm_num
    have h_mono : (2.7182818283 : ℝ)^6 < (Real.exp 1)^6 :=
      pow_lt_pow_left₀ he hpos (by norm_num)
    have h_num : (400 : ℝ) < (2.7182818283 : ℝ)^6 := by norm_num
    linarith
  -- Now we need: (1/2 * (48 * exp 6) * Λ^2) / (6 * τ * (1/120)) > 100 * Λ^2
  -- Simplify denominator: 6 * τ * (1/120) = τ / 20.
  -- LHS = (24 * exp 6 * Λ^2) / (τ/20) = (24 * 20 * exp 6 * Λ^2) / τ = 480 * exp 6 * Λ^2 / τ
  -- Need: 480 * exp 6 / τ > 100, i.e. 480 * exp 6 > 100 * τ
  -- Since τ < 1 and exp 6 > 400: 480 * exp 6 > 480 * 400 = 192000 > 100 = 100 * 1 > 100 * τ.
  have hΛ2_pos : 0 < Λ^2 := by positivity
  have hden_pos : 0 < 6 * τ * (1/120) := by
    have : (0 : ℝ) < 1/120 := by norm_num
    have h6 : (0 : ℝ) < 6 := by norm_num
    exact mul_pos (mul_pos h6 hτ_pos) this
  -- Clear the division: C < A/B ↔ C * B < A (when B > 0).
  rw [lt_div_iff₀ hden_pos]
  -- 100 * Λ^2 * (6 * τ * (1/120)) < (1/2) * (48 * exp 6) * Λ^2
  -- LHS = 100 * Λ^2 * τ / 20 = 5 * Λ^2 * τ
  -- RHS = 24 * exp 6 * Λ^2
  -- Need: 5 τ Λ² < 24 (exp 6) Λ²  ↔  5 τ < 24 exp 6  (since Λ² > 0)
  -- 24 exp 6 > 24 · 400 = 9600 ≫ 5 · 1 = 5.
  have key : 100 * Λ^2 * (6 * τ * (1 / 120)) ≤ 5 * Λ^2 * τ := by nlinarith
  have key2 : 5 * Λ^2 * τ < (1 / 2) * (48 * Real.exp 6) * Λ^2 := by
    have h1 : (1/2 : ℝ) * (48 * Real.exp 6) * Λ^2 = 24 * Real.exp 6 * Λ^2 := by ring
    rw [h1]
    -- 5 Λ² τ < 24 (exp 6) Λ²  ↔  τ < (24/5) (exp 6) (since Λ² > 0)
    -- We have τ < 1 < (24/5) · 400 < (24/5) (exp 6).
    have : 24 * Real.exp 6 * Λ^2 - 5 * Λ^2 * τ
         = Λ^2 * (24 * Real.exp 6 - 5 * τ) := by ring
    have h_pos : 0 < 24 * Real.exp 6 - 5 * τ := by
      have h1 : 24 * Real.exp 6 > 24 * 400 := by linarith
      have h2 : 5 * τ < 5 * 1 := by linarith
      linarith
    nlinarith [hΛ2_pos, h_pos]
  linarith

/-! ## Section 4: ξ_Planck — naming the Planck-cutoff scale

The "Planck cutoff" in this framework is the spectral cutoff `Λ`
(the scale at which the heat-kernel expansion is regulated).  We
record it as a definition aliasing `Λ`. -/

/-- The Planck/spectral-cutoff scale (here just an alias for the
input `Λ`). -/
def xiPlanck (Λ : ℝ) : ℝ := Λ

/-- **Sub-Planckian implies anti-diffusive.**

For any `0 < ξ < Λ` (i.e. ξ below the spectral cutoff), the
crossover scale on Route B exceeds Λ ≫ ξ, so we are well below
ξ_cross and `σ_tr(Λ; ξ) > 0`.  This is the statement that the trace
mode is anti-diffusive across the *entire* physical IR. -/
theorem sigmaTr_pos_subPlanckian (Λ ξ : ℝ) (hΛ : 0 < Λ)
    (hξ_pos : 0 < ξ) (hξ_sub : ξ < xiPlanck Λ) :
    0 < sigmaTr Λ ξ := by
  -- ξ < Λ ⇒ ξ² < Λ² < 100 Λ² < xiCrossSq Λ
  have hξ_sq_pos : 0 < ξ^2 := by positivity
  have hξΛ : ξ^2 < Λ^2 := by
    unfold xiPlanck at hξ_sub
    have hξ_le_Λ : ξ < Λ := hξ_sub
    nlinarith [hξ_pos, hΛ, hξ_le_Λ]
  have hΛ_lt_100 : Λ^2 < 100 * Λ^2 := by nlinarith [sq_nonneg Λ, hΛ]
  have h_below : ξ^2 < xiCrossSq Λ := by
    have htp := xiCrossSq_transPlanckian Λ hΛ
    linarith
  exact sigmaTr_pos_below_crossover Λ ξ hΛ hξ_sq_pos h_below

end SpectralPhysics.Cosmology

end
