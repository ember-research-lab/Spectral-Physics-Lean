/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Dark-energy equation of state `w(z)` — the self-stiffening (evolving-`w`) prediction

The framework's CC self-stiffening mechanism (EW phase transition's effect on the
CC mode) predicts an **evolving** dark-energy equation of state with
`w₀ > −1` and `w_a < 0`, consistent with DESI DR2's tentative preference for
evolving dark energy (manuscript v1.0 §`sec:self-stiffening-wz`,
`spectral-physics-latest.tex` lines 23727–23736).

## Tier classification — **Tier 4 (structural argument)**

This is the framework's LOWEST tier and is deliberately encoded as a
**hypothesis predicate**, not a derivation:
* The self-stiffening *direction* (`w₀ > −1`, `w_a < 0`) is identified by the
  mechanism, but the **quantitative** `(w₀, w_a)` requires solving the full SAGF
  fixed-point system — NOT done here and NOT in Lean anywhere.
* Accordingly `IsSelfStiffening` below is a *named hypothesis*. The theorems
  prove the **kinematic consequences** of that hypothesis (today's value, the
  past trend, distinctness from ΛCDM) — they do NOT derive the prediction.
* This module exists so the framework's evolving-`w` claim is *stated precisely
  and falsifiably* in Lean, with its conditional status explicit. See
  `results/CHAIN-RIGOR-LEDGER.md` §3.

## Falsifiability

DESI DR2 (2025) reports `w₀ ≈ −0.8 (>−1)`, `w_a ≈ −0.7 (<0)` in the `w₀waCDM`
fit — i.e. the framework's predicted *direction*. A future measurement with
`w₀ < −1` (phantom today) OR `w_a ≥ 0` (non-thawing) at high significance would
**refute** the self-stiffening direction. A confirmed `w ≡ −1` (pure ΛCDM)
would also refute it.
-/

namespace SpectralPhysics.Cosmology

/-- Chevallier–Polarski–Linder (CPL) equation of state as a function of the
    scale factor `a` (`a = 1` today, `a → 0⁺` in the past):
    `w(a) = w₀ + w_a·(1 − a)`. -/
def wCPL (w0 wa a : ℝ) : ℝ := w0 + wa * (1 - a)

/-- **Framework self-stiffening prediction (Tier-4 hypothesis):** the
    dark-energy EoS is *evolving and thawing* — quintessence-like today
    (`w₀ > −1`) and more negative in the past (`w_a < 0`). -/
def IsSelfStiffening (w0 wa : ℝ) : Prop := -1 < w0 ∧ wa < 0

/-- ΛCDM null hypothesis: a pure cosmological constant has `w ≡ −1`
    (`w₀ = −1`, `w_a = 0`). -/
def IsLambdaCDM (w0 wa : ℝ) : Prop := w0 = -1 ∧ wa = 0

/-! ## Kinematic facts about the CPL form -/

/-- Today (`a = 1`) the EoS equals `w₀`. -/
theorem wCPL_today (w0 wa : ℝ) : wCPL w0 wa 1 = w0 := by
  unfold wCPL; ring

/-- In the far past (`a = 0`) the EoS equals `w₀ + w_a`. -/
theorem wCPL_far_past (w0 wa : ℝ) : wCPL w0 wa 0 = w0 + wa := by
  unfold wCPL; ring

/-! ## Consequences of the self-stiffening hypothesis (all conditional on it) -/

/-- **Quintessence-like today.** Under self-stiffening, the present EoS is
    `> −1` (not phantom). -/
theorem today_not_phantom {w0 wa : ℝ} (h : IsSelfStiffening w0 wa) :
    -1 < wCPL w0 wa 1 := by
  rw [wCPL_today]; exact h.1

/-- **Evolving / thawing.** Under self-stiffening, the EoS was strictly more
    negative at any earlier epoch `a < 1` than today. -/
theorem more_negative_in_past {w0 wa a : ℝ}
    (h : IsSelfStiffening w0 wa) (ha : a < 1) :
    wCPL w0 wa a < wCPL w0 wa 1 := by
  unfold wCPL
  have : wa * (1 - a) < 0 := mul_neg_of_neg_of_pos h.2 (by linarith)
  linarith

/-- **Not a cosmological constant.** Self-stiffening is logically incompatible
    with pure ΛCDM (`w₀ = −1`): the framework predicts a measurably different
    EoS. -/
theorem excludes_lambdaCDM {w0 wa : ℝ} (h : IsSelfStiffening w0 wa) :
    ¬ IsLambdaCDM w0 wa := by
  rintro ⟨hw0, _⟩
  exact absurd hw0 (by have := h.1; linarith)

/-- The self-stiffening prediction is exactly the `w₀ > −1 ∧ w_a < 0` quadrant
    that DESI DR2's `w₀waCDM` fit prefers — i.e. the framework's predicted
    *direction* is the measured direction. -/
theorem matches_desi_dr2_direction {w0 wa : ℝ} (h : IsSelfStiffening w0 wa) :
    -1 < w0 ∧ wa < 0 := h

/-- **Phantom crossing (deep-past phantom case).** The CPL crossing point
    `a = 1 + (1 + w₀)/w_a` solves `w(a) = −1` exactly: when the deep-past value
    `w₀ + w_a < −1` (phantom) while `w(1) = w₀ > −1`, the affine `w(a)` crosses
    `−1`.  (The membership `a ∈ [0,1]` follows from `w₀>−1`, `w_a<0`,
    `w₀+w_a<−1`; left as a future strengthening — the equation itself is the
    content.) -/
theorem phantom_crossing_point {w0 wa : ℝ} (hwa : wa ≠ 0) :
    wCPL w0 wa (1 + (1 + w0) / wa) = -1 := by
  unfold wCPL; field_simp; ring

end SpectralPhysics.Cosmology
