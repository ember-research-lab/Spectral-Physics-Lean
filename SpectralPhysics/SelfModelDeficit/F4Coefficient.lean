/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import SpectralPhysics.SelfModelDeficit.Kappa2

/-!
# `f₄` — derived value from the Edgeworth cumulant tower

With `κ₂` pinned to 1-unit precision (`Kappa2.lean`,
`kappa2_one_unit_bracket : |κ₂_full − 529| < 1`), the Edgeworth-style
cumulant tower of v0.9 Proposition `prop:faith-tower` (line 9735)
**determines** `f₄`:

  f₂ = N · exp(κ₁)        with N = 48, κ₁ = 6  →  f₂ = 48 · e⁶
  f₄ = f₂ · exp(−κ₂/2)    Edgeworth Level-2 closure

so `f₄` is no longer an open question — it is a derived numerical
value bracketed by the Lean computation.

## The 55-orders-of-magnitude conflict

The v0.9 manuscript carries two readings of `f₄`:

* **Edgeworth reading** (this file): `f₄ = f₂ · exp(−κ₂/2)` at
  `κ₂ ≈ 529.421`, giving  `f₄ ≈ 2.11 · 10⁻¹¹¹`.
* **`5 e⁶` reading** (v0.9 §27.6, contested in audits): a single-mode
  `f₄ = 5 · e⁶ ≈ 2017`, treated as a placeholder dimensional estimate.

These two readings differ by **≈ 114 orders of magnitude**.  The
"55-orders contradiction" of `top10.md` line 222 is the gap between
the v0.9 reading `5 e⁶` and the *cosmological-target* `Λ_obs/M_Pl² ~
10⁻¹²¹` — same phenomenon viewed against a different yardstick.

**The Lean settlement.**  The Edgeworth reading is mathematically
derived from `κ₂` and `κ₁` via Proposition `prop:faith-tower`, while
`5 e⁶` is a quoted estimate without a closed-form derivation in the
manuscript.  Once `κ₂` is pinned numerically (this branch), the
Edgeworth reading becomes `2.11 · 10⁻¹¹¹` to better than 0.01-unit
precision, and the `5 e⁶` reading is **falsified** at > 100 natural-log
units of separation (> 43 orders of magnitude).

## Tier classification

* **Tier 1 (proved here)**: `f₂ = 48 · e⁶`; the Edgeworth identity
  `f₄ = f₂ · exp(−κ₂/2)`; `log f₄ < −254` (so `f₄ < e⁻²⁵⁴ < 10⁻¹¹⁰`);
  `log f₄ + 100 < log (5 e⁶)`, falsifying the `5 e⁶` reading.
* **Tier 2**: nothing new — all numerical content flows from the
  `κ₂` axioms in `Kappa2.lean` (which themselves have *no* sorrys
  on this branch — they are all closed-form).

## References

* Ben-Shalom, "Spectral Physics", v0.9, Proposition `prop:faith-tower`
  (line 9735).
* `pre_geometric/computable_inventory/top10.md` Rank 6 (this branch's
  task) and "Honourable mentions" #13 (this file's task).
-/

namespace SpectralPhysics.SelfModelDeficit

open Real

/-! ## The Edgeworth tower constants -/

/-- The visible-Yukawa mode count entering `f₂`.  Distinct from the
    `NVis = 96` of `Kappa2.lean`: here only the 48 *Yukawa* modes
    enter (the 48 aux modes contribute to `κ₂` but not to `f₂`). -/
def NYuk : ℕ := 48

/-- The Edgeworth tower's first cumulant `κ₁ = 6 = mean of −log y_f`
    over the 48 visible-Yukawa modes (Baker-form construction). -/
noncomputable def kappa1 : ℝ := 6

/-- `f₂ = N · exp(κ₁) = 48 · e⁶`, the v0.9 Level-1 prediction
    (Proposition `prop:faith-tower`). -/
noncomputable def f_2 : ℝ := (NYuk : ℝ) * Real.exp kappa1

/-- `f₂ = 48 · e⁶`. -/
theorem f_2_value : f_2 = 48 * Real.exp 6 := by
  unfold f_2 NYuk kappa1; norm_num

/-- `f₂ > 0`. -/
theorem f_2_pos : 0 < f_2 := by
  rw [f_2_value]
  exact mul_pos (by norm_num) (Real.exp_pos _)

/-! ## The Level-2 Edgeworth closure -/

/-- The Edgeworth-style Level-2 closure
    `f₄ = f₂ · exp(−κ₂/2)`, with `κ₂` from the law-of-total-variance
    decomposition in `Kappa2.lean`. -/
noncomputable def f_4 : ℝ := f_2 * Real.exp (-(kappa2_full / 2))

/-- `f₄ > 0` from `f₂ > 0` and `exp > 0`. -/
theorem f_4_pos : 0 < f_4 := by
  unfold f_4
  exact mul_pos f_2_pos (Real.exp_pos _)

/-- The Edgeworth definition: `log f₄ = log f₂ − κ₂/2`. -/
theorem log_f_4_eq :
    Real.log f_4 = Real.log f_2 - kappa2_full / 2 := by
  unfold f_4
  rw [Real.log_mul (ne_of_gt f_2_pos) (Real.exp_ne_zero _),
      Real.log_exp]
  ring

/-! ## Bounds on `log f₂` and `log f₄`

We use the standard Mathlib bound `Real.exp_one_gt_d9 : 2.7182818283 < e`
to get coarse log/exp inequalities. -/

/-- `Real.exp 6 > 400`.  Sufficient for the `f₂` lower bound. -/
theorem exp_6_gt_400 : (400 : ℝ) < Real.exp 6 := by
  -- exp 6 = (exp 1)^6, and exp 1 > 2.7182818283.
  -- (2.7182818283)^6 > 403, so > 400 with comfortable margin.
  have h_e : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h_e_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  have hexp6 : Real.exp 6 = (Real.exp 1) ^ 6 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hexp6]
  have h_pos : (0 : ℝ) < 2.7182818283 := by norm_num
  -- 2.7182818283^6 > 400 by direct computation
  have h_pow : (400 : ℝ) < (2.7182818283 : ℝ) ^ 6 := by norm_num
  exact lt_of_lt_of_le h_pow (pow_le_pow_left₀ (by norm_num) h_e.le 6)

/-- `Real.exp 6 < 405`.  Sufficient for the `f₂` upper bound. -/
theorem exp_6_lt_405 : Real.exp 6 < 405 := by
  have h_e : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hexp6 : Real.exp 6 = (Real.exp 1) ^ 6 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [hexp6]
  have h_pos : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos _).le
  have h_pow : (Real.exp 1) ^ 6 ≤ (2.7182818286 : ℝ) ^ 6 :=
    pow_le_pow_left₀ h_pos h_e.le 6
  have h_num : (2.7182818286 : ℝ) ^ 6 < 405 := by norm_num
  linarith

/-- `f₂ > 19200` (tight enough for our purposes; actual ≈ 19365). -/
theorem f_2_gt_19200 : (19200 : ℝ) < f_2 := by
  rw [f_2_value]
  have h := exp_6_gt_400
  -- 48 * exp 6 > 48 * 400 = 19200
  nlinarith [Real.exp_pos (6 : ℝ)]

/-- `f₂ < 19440` (tight enough for our purposes; actual ≈ 19365). -/
theorem f_2_lt_19440 : f_2 < 19440 := by
  rw [f_2_value]
  have h := exp_6_lt_405
  nlinarith [Real.exp_pos (6 : ℝ)]

/-- `log 19440 < 10`. -/
theorem log_19440_lt_10 : Real.log 19440 < 10 := by
  -- log 19440 < log e^10 = 10 ⟺ 19440 < e^10
  -- e^10 = (e^1)^10 > 2.7182^10 > 22000 > 19440
  have h_e : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hexp10 : Real.exp 10 = (Real.exp 1) ^ 10 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h_e_pos : (0 : ℝ) ≤ 2.7182818283 := by norm_num
  have h_pow : (22000 : ℝ) < (2.7182818283 : ℝ) ^ 10 := by norm_num
  have h_e10 : (22000 : ℝ) < Real.exp 10 := by
    rw [hexp10]
    exact lt_of_lt_of_le h_pow (pow_le_pow_left₀ h_e_pos h_e.le 10)
  have h_e10_gt_19440 : (19440 : ℝ) < Real.exp 10 := by linarith
  rw [show (10 : ℝ) = Real.log (Real.exp 10) by rw [Real.log_exp]]
  exact Real.log_lt_log (by norm_num) h_e10_gt_19440

/-- `log f₂ < 10`. -/
theorem log_f_2_upper : Real.log f_2 < 10 := by
  have h1 : f_2 < 19440 := f_2_lt_19440
  have h2 : (0 : ℝ) < f_2 := f_2_pos
  have h3 : Real.log f_2 < Real.log 19440 :=
    Real.log_lt_log h2 h1
  linarith [log_19440_lt_10]

/-- `Real.exp 3 < 48`. -/
theorem exp_3_lt_48 : Real.exp 3 < 48 := by
  have h_e : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hexp3 : Real.exp 3 = (Real.exp 1) ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [hexp3]
  have h_pos : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos _).le
  have h_pow : (Real.exp 1) ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 :=
    pow_le_pow_left₀ h_pos h_e.le 3
  have h_num : (2.7182818286 : ℝ) ^ 3 < 48 := by norm_num
  linarith

/-- `log 48 > 3`. -/
theorem log_48_gt_3 : 3 < Real.log 48 := by
  have h := exp_3_lt_48
  rw [show (3 : ℝ) = Real.log (Real.exp 3) by rw [Real.log_exp]]
  exact Real.log_lt_log (Real.exp_pos _) h

/-- `log f₂ > 9`.  From `f₂ = 48 · e⁶`, `log f₂ = log 48 + 6 > 3 + 6 = 9`. -/
theorem log_f_2_gt_9 : 9 < Real.log f_2 := by
  rw [f_2_value, Real.log_mul (by norm_num : (48 : ℝ) ≠ 0)
        (Real.exp_ne_zero _), Real.log_exp]
  linarith [log_48_gt_3]

/-- `f₂ ≤ 48 · e⁶ + 1`, a trivial upper bound (we won't need a tight one). -/
theorem f_2_le_48_e6_succ : f_2 ≤ 48 * Real.exp 6 + 1 := by
  rw [f_2_value]; linarith

/-! ## Headline brackets on `log f₄` -/

/-- **Headline upper.**  `log f₄ < −254`, equivalently `f₄ < e⁻²⁵⁴`.

    Combines `log f₂ < 10` and `κ₂_full > 529.42`. -/
theorem log_f_4_lt_neg_254 : Real.log f_4 < -254 := by
  rw [log_f_4_eq]
  have h1 : Real.log f_2 < 10 := log_f_2_upper
  have h2 : (52942 / 100 : ℝ) < kappa2_full := kappa2_above_529_42
  -- log f_4 = log f_2 − κ_2/2 < 10 − 529.42/2 = 10 − 264.71 = −254.71
  linarith

/-- **Headline lower.**  `log f₄ > −256`.

    From `log f₂ > 9` (`log_f_2_gt_9`) and `κ₂_full < 529.43`
    (`kappa2_below_529_43`):
      log f_4 = log f_2 − κ_2/2 > 9 − 529.43/2 = 9 − 264.715 = −255.715. -/
theorem log_f_4_gt_neg_256 : -256 < Real.log f_4 := by
  rw [log_f_4_eq]
  have h1 : 9 < Real.log f_2 := log_f_2_gt_9
  have h2 : kappa2_full < 52943 / 100 := kappa2_below_529_43
  linarith

/-! ## The 55-orders-of-magnitude conflict resolution -/

/-- The candidate v0.9 reading of `f₄`. -/
noncomputable def f_4_v09_reading : ℝ := 5 * Real.exp 6

/-- `5 · e⁶ > 2000`. -/
theorem f_4_v09_reading_gt_2000 : 2000 < f_4_v09_reading := by
  unfold f_4_v09_reading
  have h := exp_6_gt_400
  nlinarith

/-- `log (5 · e⁶) > 7`.  Concretely, `log 5 + 6 > 7 ⟺ log 5 > 1`.
    Since `5 > e ≈ 2.718`, `log 5 > log e = 1`. -/
theorem log_f_4_v09_gt_7 : 7 < Real.log f_4_v09_reading := by
  unfold f_4_v09_reading
  rw [Real.log_mul (by norm_num : (5:ℝ) ≠ 0) (Real.exp_ne_zero _),
      Real.log_exp]
  -- log 5 + 6 > 7 ⟺ log 5 > 1 ⟺ 5 > e
  have h_e_lt_5 : Real.exp 1 < 5 := by
    have := Real.exp_one_lt_d9; linarith
  have h_log5 : 1 < Real.log 5 := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    exact Real.log_lt_log (Real.exp_pos _) h_e_lt_5
  linarith

/-- **Settlement theorem.**  The two readings disagree: their
    natural logs differ by more than 100 (so `f₄_v09 / f₄ > e¹⁰⁰`,
    equivalently > 10⁴³). -/
theorem f_4_readings_inconsistent :
    Real.log f_4 + 100 < Real.log f_4_v09_reading := by
  have h_edge : Real.log f_4 < -254 := log_f_4_lt_neg_254
  have h_v09 : 7 < Real.log f_4_v09_reading := log_f_4_v09_gt_7
  -- log f_4 + 100 < -254 + 100 = -154 < 7 < log f_4_v09
  linarith

/-- **The Lean verdict on `f₄`.**

    1. `κ₂` is pinned to 1-unit precision (`Kappa2.kappa2_one_unit_bracket`).
    2. `f₄ = f₂ · exp(−κ₂/2)` with `f₂ = 48 e⁶` (Edgeworth, derivable).
    3. `log f₄ < −254` (this branch's headline; see `log_f_4_lt_neg_254`).
    4. `f₄ ≠ 5 · e⁶`: the readings disagree by > 100 in natural-log
       units (`f_4_readings_inconsistent`), i.e. > 43 orders of magnitude.

    **Conclusion**: the Edgeworth reading is the framework's standing
    prediction for `f₄`; the `5 · e⁶` reading is falsified.
-/
theorem f_4_verdict :
    Real.log f_4 < -254 ∧
    7 < Real.log f_4_v09_reading ∧
    Real.log f_4 + 100 < Real.log f_4_v09_reading :=
  ⟨log_f_4_lt_neg_254, log_f_4_v09_gt_7, f_4_readings_inconsistent⟩

/-! ## Honest negative — the Edgeworth route does NOT close the CC magnitude -/

/-- `Λ_obs / M_Pl² ≈ 2.76×10⁻¹²¹` (Planck 2018), so its natural log is
    `≈ −277.6`.  We use `−277` as a deliberately *conservative* (upper) bound,
    which makes the overshoot proved below an UNDER-statement of the true
    residual (`≈ 21.6`–`23.6` nat-log units, i.e. ~9–10 orders of magnitude). -/
noncomputable def cc_log_target : ℝ := -277

/-- **Honest negative (2026-05-26 rigor audit): the Edgeworth `f₄` route does
    NOT predict the cosmological-constant magnitude.**

    `f₄ = f₂·exp(−κ₂/2)` has `log f₄ ∈ (−256, −254)` (`log_f_4_{gt,lt}` above),
    whereas the cosmological target `Λ_obs/M_Pl² ≈ 10⁻¹²¹` has
    `ln ≈ −277.6`.  Hence `log f₄ − ln(Λ_obs/M_Pl²) > 20`: the honest cumulant
    coefficient is **more than `e²⁰` (≳ 8 orders of magnitude) too large** to be
    `Λ_obs/M_Pl²`.

    Consequently the framework's CC "closure" does **not** flow from this `f₄`;
    it relies on a `κ₂` *tuned to* `Λ_obs` (`Kappa2.lean` docstring line 49:
    `κ₂ = 2·ln(Λ_c²/Λ_obs)`), i.e. the chain runs `Λ_obs → κ₂`, not the reverse.
    This theorem machine-records the residual so the non-closure is a proved
    artifact, not prose.  See `results/CHAIN-RIGOR-LEDGER.md`. -/
theorem f4_overshoots_cc_target : Real.log f_4 - cc_log_target > 20 := by
  have h := log_f_4_gt_neg_256
  unfold cc_log_target
  linarith

end SpectralPhysics.SelfModelDeficit
