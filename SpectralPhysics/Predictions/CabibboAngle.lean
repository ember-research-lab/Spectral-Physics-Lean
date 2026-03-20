/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Triad.SelfReferentialTriad

/-!
# The Cabibbo Parameter from Self-Reference

λ = (150 - 23√5) / 440 ≈ 0.2240

Measured: |V_us| = 0.2243 ± 0.0005. Agreement: 0.12%.

This is the most precise numerical prediction of the spectral framework.

## Derivation

1. Stability bound: total accumulated mixing λ/(1-λ) ≤ τ
2. Saturation: λ₀ = τ/(1+τ)
3. Discrete correction: 2³ = 8 microstates from 3 generations
4. Result: λ = τ(8+τ) / [8(1+τ)]
5. Substituting τ = (5-√5)/10 gives (150-23√5)/440

## References

* Ben-Shalom, "Spectral Physics", Theorem 40.2 (Cabibbo Parameter)
-/

noncomputable section

open Real

/-- The Cabibbo parameter derived from self-referential tolerance.

λ = τ(8+τ) / [8(1+τ)]

This is the mixing strength at which the self-referential system
saturates its tolerance: any more mixing would destabilize self-reference. -/
def cabibboParam : ℝ := τ * (8 + τ) / (8 * (1 + τ))

/-- The Cabibbo parameter in closed form -/
theorem cabibbo_closed_form :
    cabibboParam = (150 - 23 * Real.sqrt 5) / 440 := by
  -- STRATEGY: Substitute τ = (5-√5)/10 (from tau_closed_form) into
  --   cabibboParam = τ(8+τ) / [8(1+τ)]
  --
  -- Let s = √5. Then τ = (5-s)/10.
  -- 8 + τ = 8 + (5-s)/10 = (80+5-s)/10 = (85-s)/10
  -- 1 + τ = 1 + (5-s)/10 = (10+5-s)/10 = (15-s)/10
  -- τ(8+τ) = (5-s)(85-s)/100
  -- 8(1+τ) = 8(15-s)/10 = 4(15-s)/5
  -- Ratio = (5-s)(85-s)/100 · 5/(4(15-s)) = (5-s)(85-s)/(80(15-s))
  --
  -- Numerator: (5-s)(85-s) = 425 - 5s - 85s + s² = 425 - 90s + 5 = 430 - 90s
  -- Denominator: 80(15-s) = 1200 - 80s
  --
  -- So cabibboParam = (430-90s)/(1200-80s)
  -- Simplify by dividing num and denom by 2: (215-45s)/(600-40s)
  -- Hmm, that doesn't immediately give (150-23s)/440.
  -- Let me recheck...
  --
  -- Actually: (430-90√5) / (1200-80√5)
  -- Multiply top and bottom by ... let me just compute (150-23√5)/440 directly.
  -- (150-23·2.236)/440 = (150-51.43)/440 = 98.57/440 = 0.2240 ✓
  -- (430-90·2.236)/(1200-80·2.236) = (430-201.2)/(1200-178.9) = 228.8/1021.1 = 0.2241
  -- Hmm, close but not exact? Let me recompute more carefully.
  --
  -- τ = (5-√5)/10 ≈ 0.27639
  -- 8+τ ≈ 8.27639
  -- 1+τ ≈ 1.27639
  -- τ(8+τ)/[8(1+τ)] = 0.27639·8.27639/(8·1.27639) = 2.2870/10.2111 = 0.22397
  -- (150-23√5)/440 = (150-51.426)/440 = 98.574/440 = 0.22403
  --
  -- These don't match! There may be an error in the manuscript's closed form
  -- or in my expansion. Need to verify algebraically:
  -- τ(8+τ)/[8(1+τ)] with τ = (5-√5)/10
  -- = [(5-√5)/10]·[8+(5-√5)/10] / [8·(1+(5-√5)/10)]
  -- = [(5-√5)/10]·[(85-√5)/10] / [8·(15-√5)/10]
  -- = (5-√5)(85-√5)/100 / [8(15-√5)/10]
  -- = (5-√5)(85-√5) / [80(15-√5)]
  --
  -- (5-√5)(85-√5) = 425 - 5√5 - 85√5 + 5 = 430 - 90√5
  -- 80(15-√5) = 1200 - 80√5
  --
  -- So we need: (430-90√5)/(1200-80√5) = (150-23√5)/440
  -- Cross multiply: 440(430-90√5) = (150-23√5)(1200-80√5)
  -- LHS: 189200 - 39600√5
  -- RHS: 180000 - 12000√5 - 27600√5 + 23·80·5 = 180000 - 39600√5 + 9200
  --     = 189200 - 39600√5 ✓
  --
  -- Great, it checks out! The cross-multiplication identity is the proof.
  --
  simp only [cabibboParam]
  rw [tau_closed_form]
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hs_pos : Real.sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
  have hd1 : (8 : ℝ) * (1 + (5 - Real.sqrt 5) / 10) ≠ 0 := by
    have h5_bound : Real.sqrt 5 < 3 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
    have : (0 : ℝ) < 8 * (1 + (5 - Real.sqrt 5) / 10) := by nlinarith [hs_pos]
    linarith
  have hd2 : (440 : ℝ) ≠ 0 := by norm_num
  rw [div_eq_div_iff hd1 hd2]
  nlinarith [hsq, hs_pos, sq_nonneg (Real.sqrt 5)]

/-- The leading-order Cabibbo parameter (without discrete correction) -/
def cabibboLeading : ℝ := τ / (1 + τ)

/-- The discrete correction factor -/
def discreteCorrection : ℝ := (8 + τ) / 8

/-- cabibboParam = cabibboLeading * discreteCorrection -/
theorem cabibbo_factored :
    cabibboParam = cabibboLeading * discreteCorrection := by
  simp only [cabibboParam, cabibboLeading, discreteCorrection]
  have hd : (1 : ℝ) + τ ≠ 0 := by
    have : τ > 0 := by simp only [τ]; unfold φ; positivity
    linarith
  field_simp [hd]

/-- Numerical approximation -/
theorem cabibbo_approx :
    |cabibboParam - 0.2240| < 0.001 := by
  rw [cabibbo_closed_form]
  have h5_lo : (2.2360 : ℝ) < Real.sqrt 5 := by
    rw [show (2.2360 : ℝ) = Real.sqrt (2.2360 ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.2360)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h5_hi : Real.sqrt 5 < (2.2361 : ℝ) := by
    rw [show (2.2361 : ℝ) = Real.sqrt (2.2361 ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.2361)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [abs_lt]
  constructor <;> linarith

/-- The most precise prediction: 0.12% agreement with |V_us| -/
theorem cabibbo_agreement :
    let predicted := cabibboParam
    let measured := (0.2243 : ℝ)
    |predicted - measured| / measured < 0.002 := by
  simp only
  rw [cabibbo_closed_form]
  have h5_lo : (2.2360 : ℝ) < Real.sqrt 5 := by
    rw [show (2.2360 : ℝ) = Real.sqrt (2.2360 ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.2360)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h5_hi : Real.sqrt 5 < (2.2361 : ℝ) := by
    rw [show (2.2361 : ℝ) = Real.sqrt (2.2361 ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.2361)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 0.2243)]
  rw [abs_lt]
  constructor <;> nlinarith

end
