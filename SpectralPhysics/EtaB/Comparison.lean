/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.EtaB.Formulas

/-!
# Comparison of Formula A and Formula B against the Planck 2018 value

We bracket each formula's numerical value, then state the deviations
from the observed cosmic baryon-to-photon ratio.

## Numerical summary (verified independently)

* `λ_C   ≈ 0.224024` (Cabibbo, framework-derived)
* `λ_C^14 ≈ 8.019 × 10⁻¹⁰`        — this is **Formula A**
* `J²/2  = 4.5 × 10⁻¹⁰`           — this is **Formula B**
* `η_B^obs = 6.10 × 10⁻¹⁰`        — Planck 2018

Formula A overshoots; Formula B undershoots.  Both are off by roughly
the same magnitude (`1.6` vs `1.9` × 10⁻¹⁰), but Formula B is closer
in absolute terms.

> ⚠️  **Honest caveat exposed by Lean.**  The task spec quoted
>     Formula A as giving `≈ 4.4 × 10⁻¹⁰`.  Direct numerical
>     evaluation of `(0.224024)^14` instead gives `≈ 8.02 × 10⁻¹⁰`,
>     i.e. roughly *twice* the value the prior text-only audit
>     reported.  This means Formula A and Formula B are *not*
>     numerically very close — Formula A is on the *opposite side*
>     of the observed value from Formula B.  See `STATUS.md`.

## What Lean computes vs. what is axiomatized

* `etaB_FormulaA = λ_C^14` is bracketed
  `7.9 × 10⁻¹⁰ < etaB_FormulaA < 8.1 × 10⁻¹⁰` as a **Tier-1
  theorem** chain: the closed form `λ_C = (150 − 23·√5)/440`
  combined with the manual `√5`-bracketing pattern from
  `cabibbo_agreement` gives the tightened `0.22397 < λ_C < 0.22403`,
  and `pow_lt_pow_left` plus `norm_num` lifts this through the 14th
  power.  No numerical axiom is required.
* `etaB_FormulaB = J²/2` is computed *directly* from `Jarlskog_value`
  and `ring` to give the exact value `4.5 × 10⁻¹⁰` — Tier 1.
* `etaB_observed` and `etaB_observed_value` are named axioms
  (Planck 2018 satellite measurement; not derivable in Lean).

## References

* Planck Collaboration, *Planck 2018 results. VI. Cosmological
  parameters*, A&A 641 (2020) A6, table 2 (`100 Ω_b h² = 2.237 ±
  0.015`, equivalent to `η_B = (6.12 ± 0.04) × 10⁻¹⁰`).
* PDG 2024 CKM review: `J = 3.00^{+0.15}_{-0.09} × 10⁻⁵`.
-/

namespace SpectralPhysics.EtaB

noncomputable section

open Real

/-! ## Observed value (named axiom: Planck 2018) -/

/-- **Named axiom (observational input).**

    The cosmic baryon-to-photon ratio measured by the Planck satellite.
    Central value `η_B = 6.10 × 10⁻¹⁰` (Planck 2018, A&A 641 A6, table 2,
    extracted from `100 Ω_b h² = 2.237 ± 0.015`). -/
axiom etaB_observed : ℝ

/-- The Planck 2018 central value, `η_B^obs = 6.10 × 10⁻¹⁰`. -/
axiom etaB_observed_value : etaB_observed = 6.10e-10

/-! ## Formula A numerical bracket (Tier 1 — fully derived)

    `λ_C^14 ≈ 8.019 × 10⁻¹⁰`.  We chain:

    1. `cabibbo_closed_form`: `λ_C = (150 − 23·√5)/440`.
    2. Manual `√5`-bracketing (`2.236 < √5 < 2.237`, the same pattern
       used by `cabibbo_agreement`) gives the tight Cabibbo bracket
       `0.22397 < λ_C < 0.22403`.
    3. `pow_lt_pow_left₀` lifts the inequality through the 14th power.
    4. `norm_num` evaluates the rational endpoints
       `(0.22397)^14 ≈ 7.992 × 10⁻¹⁰` and
       `(0.22403)^14 ≈ 8.022 × 10⁻¹⁰`.

    Result: `7.9 × 10⁻¹⁰ < λ_C^14 < 8.1 × 10⁻¹⁰`, fully Tier 1. -/

/-- **Lemma (Tier 1).**  Cabibbo lower bound from `cabibbo_approx`. -/
theorem cabibbo_gt_223 : (0.223 : ℝ) < cabibboParam := by
  have h := cabibbo_approx
  rw [abs_lt] at h
  linarith

/-- **Lemma (Tier 1).**  Cabibbo upper bound from `cabibbo_approx`. -/
theorem cabibbo_lt_225 : cabibboParam < (0.225 : ℝ) := by
  have h := cabibbo_approx
  rw [abs_lt] at h
  linarith

/-- **Lemma (Tier 1).**  Tighter Cabibbo lower bound, derived from
    the closed form `cabibboParam = (150 − 23√5)/440` together with
    `√5 < 2.237`.  Numerically `cabibboParam > 0.22397`. -/
theorem cabibbo_gt_22397 : (0.22397 : ℝ) < cabibboParam := by
  rw [cabibbo_closed_form]
  have h5 : Real.sqrt 5 < (2.237 : ℝ) := by
    rw [show (2.237 : ℝ) = Real.sqrt (2.237 ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.237)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- (150 - 23·2.237)/440 = 98.549/440 = 0.223975
  -- need 0.22397 < (150 - 23·√5)/440  iff  0.22397·440 < 150 - 23·√5
  --                                   iff  98.5468 + 23·√5 < 150
  --                                   iff  23·√5 < 51.4532
  --                                   iff  √5 < 51.4532/23 = 2.23709...
  -- since √5 < 2.237 < 2.23709, OK
  have h440 : (440 : ℝ) > 0 := by norm_num
  rw [lt_div_iff₀ h440]
  linarith

/-- **Lemma (Tier 1).**  Tighter Cabibbo upper bound:
    `cabibboParam < 0.22403`. -/
theorem cabibbo_lt_22403 : cabibboParam < (0.22403 : ℝ) := by
  rw [cabibbo_closed_form]
  have h5 : (2.236 : ℝ) < Real.sqrt 5 := by
    rw [show (2.236 : ℝ) = Real.sqrt (2.236 ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.236)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- (150 - 23·2.236)/440 = 98.572/440 = 0.22402727...
  -- need (150 - 23·√5)/440 < 0.22403
  --      iff 150 - 23·√5 < 0.22403·440 = 98.5732
  --      iff 51.4268 < 23·√5
  --      iff 2.23595... < √5
  -- since √5 > 2.236 > 2.23596, OK
  have h440 : (440 : ℝ) > 0 := by norm_num
  rw [div_lt_iff₀ h440]
  linarith

/-- **Theorem (Tier 1).**  Upper bound `λ_C^14 < 8.1 × 10⁻¹⁰`.

    Numerically `(0.22403)^14 ≈ 8.022 × 10⁻¹⁰ < 8.1 × 10⁻¹⁰`. -/
theorem etaB_FormulaA_upper : etaB_FormulaA < 8.1e-10 := by
  unfold etaB_FormulaA lambdaC
  have h_pos : 0 ≤ cabibboParam := le_of_lt (by
    unfold cabibboParam
    have hτ : 0 < τ := by simp only [τ]; unfold φ; positivity
    positivity)
  have h_lt : cabibboParam < 0.22403 := cabibbo_lt_22403
  have h_pow : cabibboParam ^ 14 < (0.22403 : ℝ) ^ 14 :=
    pow_lt_pow_left₀ h_lt h_pos (by decide)
  have h_eval : (0.22403 : ℝ) ^ 14 < 8.1e-10 := by norm_num
  linarith

/-- **Theorem (Tier 1).**  Lower bound `7.9 × 10⁻¹⁰ < λ_C^14`.

    Numerically `(0.22397)^14 ≈ 7.992 × 10⁻¹⁰ > 7.9 × 10⁻¹⁰`. -/
theorem etaB_FormulaA_lower : 7.9e-10 < etaB_FormulaA := by
  unfold etaB_FormulaA lambdaC
  have h_pos : (0 : ℝ) ≤ 0.22397 := by norm_num
  have h_lt : (0.22397 : ℝ) < cabibboParam := cabibbo_gt_22397
  have h_pow : (0.22397 : ℝ) ^ 14 < cabibboParam ^ 14 :=
    pow_lt_pow_left₀ h_lt h_pos (by decide)
  have h_eval : 7.9e-10 < (0.22397 : ℝ) ^ 14 := by norm_num
  linarith

/-- Formula A produces a value *strictly greater* than the observed
    `η_B`.  This is the surprising fact that Lean exposes:
    `λ^14 > η_B^obs`, contrary to the `≈ 4.4 × 10⁻¹⁰` figure quoted
    in the task spec. -/
theorem etaB_FormulaA_gt_observed : etaB_observed < etaB_FormulaA := by
  rw [etaB_observed_value]
  have h := etaB_FormulaA_lower
  linarith

/-! ## Formula B numerical bracket (Tier 1 — derived) -/

/-- The exact closed value of Formula B, given the PDG Jarlskog axiom:
    `etaB_FormulaB = (3 × 10⁻⁵)² / 2 = 4.5 × 10⁻¹⁰`. -/
theorem etaB_FormulaB_exact : etaB_FormulaB = 4.5e-10 := by
  unfold etaB_FormulaB
  rw [Jarlskog_value]
  ring

/-- Formula B produces a value *strictly less than* the observed `η_B`. -/
theorem etaB_FormulaB_lt_observed : etaB_FormulaB < etaB_observed := by
  rw [etaB_observed_value, etaB_FormulaB_exact]
  norm_num

/-! ## Sign of deviation: A overshoots, B undershoots -/

/-- The (signed) excess of Formula A over the observed value
    (positive: Formula A overshoots). -/
noncomputable def excessA : ℝ := etaB_FormulaA - etaB_observed

/-- The (signed) deficit of Formula B from the observed value
    (positive: Formula B undershoots). -/
noncomputable def deficitB : ℝ := etaB_observed - etaB_FormulaB

theorem excessA_pos : 0 < excessA := by
  unfold excessA
  have := etaB_FormulaA_gt_observed; linarith

theorem deficitB_pos : 0 < deficitB := by
  unfold deficitB
  have := etaB_FormulaB_lt_observed; linarith

/-- Formula A's excess lies in `(1.8 × 10⁻¹⁰, 2.0 × 10⁻¹⁰)`. -/
theorem excessA_bracket :
    1.8e-10 < excessA ∧ excessA < 2.0e-10 := by
  unfold excessA
  rw [etaB_observed_value]
  refine ⟨?_, ?_⟩
  · have := etaB_FormulaA_lower; linarith
  · have := etaB_FormulaA_upper; linarith

/-- Formula B's deficit is exactly `1.6 × 10⁻¹⁰`. -/
theorem deficitB_exact : deficitB = 1.6e-10 := by
  unfold deficitB
  rw [etaB_observed_value, etaB_FormulaB_exact]
  ring

/-! ## Absolute deviations -/

/-- `|η_B^A − η_B^obs|` equals `excessA`. -/
theorem abs_dev_A : |etaB_FormulaA - etaB_observed| = excessA := by
  unfold excessA
  exact abs_of_pos (by have := etaB_FormulaA_gt_observed; linarith)

/-- `|η_B^B − η_B^obs|` equals `deficitB`. -/
theorem abs_dev_B : |etaB_FormulaB - etaB_observed| = deficitB := by
  unfold deficitB
  rw [show etaB_FormulaB - etaB_observed = -(etaB_observed - etaB_FormulaB) by ring,
      abs_neg]
  exact abs_of_pos (by have := etaB_FormulaB_lt_observed; linarith)

/-! ## The verdict at the comparison level -/

/-- **Theorem (Tier 1).**  Formula B's deficit is smaller in
    magnitude than Formula A's excess:
    `|dev_B| = 1.6 × 10⁻¹⁰` (exact)
    `|dev_A| ∈ (1.8 × 10⁻¹⁰, 2.0 × 10⁻¹⁰)`. -/
theorem deficitB_lt_excessA : deficitB < excessA := by
  rw [deficitB_exact]
  have ⟨h_lo, _⟩ := excessA_bracket
  linarith

/-- **Theorem (Tier 1).**  Formula B's |deviation| is strictly smaller
    than Formula A's |deviation|. -/
theorem abs_deviation_compare :
    |etaB_FormulaB - etaB_observed| < |etaB_FormulaA - etaB_observed| := by
  rw [abs_dev_A, abs_dev_B]
  exact deficitB_lt_excessA

end

end SpectralPhysics.EtaB
