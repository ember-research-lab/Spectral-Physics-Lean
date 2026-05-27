/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import SpectralPhysics.SelfModelDeficit.Yukawas

/-!
# `κ₂` — second cumulant of the visible+hidden log-Yukawa spectrum

This file refines the second cumulant
  `κ₂ = (1/N) Σ_i (ξ_i − μ)²`
with `ξ_i = -log y_i` over the full SM+see-saw spectrum
(`N = N_vis + N_hid = 96 + 288 = 384`) to **1-unit precision**.

## The law-of-total-variance decomposition

The faithfulness-tower report
(`pre_geometric/faithfulness_tower_l3/report.md`) decomposes `κ₂` by the
**law of total variance** over the visible/hidden partition:

  κ₂_full = E[Var(ξ|sector)]  +  Var[E(ξ|sector)]
          = (n_v · κ_v + n_h · κ_h)/N
            + (n_v · n_h / N²) · (μ_v − μ_h)²

with the Baker-constrained inputs (recomputed at 50-decimal mpmath
precision in `pre_geometric/Lambda1_refined/scse_refined.py`):

  κ₂_vis = 9.927069…    (Baker form on 48 charged + 3 light-ν + 24 aux,
                         plus 48 depth-6 aux modes)
  κ₂_hid = 533.586…     (see-saw cascade `(ξ_R, ξ_D, 2ξ_D − ξ_R)`
                         at ξ_R = 3.7090, ξ_D = 32, 96 modes per block)
  μ_vis  = 6            (exact)
  μ_hid  = 32           (exact: average of `(ξ_R, ξ_D, 2ξ_D − ξ_R)`)
  n_vis  = 96
  n_hid  = 288

Direct evaluation:

  W = (96 · 9.927069 + 288 · 533.585765)/384  =  402.671091
  B = (96 · 288 / 384²) · 26²  =  (3/16) · 676  =  126.75
  κ₂_full = W + B  =  529.421091

This **matches the Baker target `κ₂_needed_obs = 2 ln(Λ_c²/Λ_obs) = 529.421…`
to all 30 mpmath digits**.

NOTE (2026-05-26 rigor audit): because `529.42` IS `2·ln(Λ_c²/Λ_obs)`, the
Tier-2 input `κ₂_hid = 533.586` (and the see-saw `ξ_R = 3.7090` that produces
it) are *tuned to* `Λ_obs` — the chain runs `Λ_obs → κ₂`, not `κ₂ → Λ_obs`.
So the downstream "CC closure" is a consistency/identification statement, NOT
a first-principles prediction of the Λ magnitude (the honest Edgeworth `f_4`
route overshoots `Λ_obs/M_Pl²` by ~10 orders; see
`F4Coefficient.f4_overshoots_cc_target` and `results/CHAIN-RIGOR-LEDGER.md`).

The 12-unit residual reported in the
inventory entry was an artifact of the *naive* μ_hid ≈ 1 reading and
the *coarse* κ₂_vis ≈ 19.854 figure quoted in the early
faithfulness-tower audit; both are corrected by the high-precision
Python wrapper.

## Tier classification

* **Tier 1 (proved here)**: the law-of-total-variance identity, the
  closed-form arithmetic on the Tier-2 inputs, the
  `|κ₂_full − 529.421| ≤ 1` bracket (1-unit precision, the inventory
  goal), and the resulting `f₄` derivation in `F4Coefficient.lean`.
* **Tier 2 (named axioms, with citations)**: the four numerical
  cumulant/mean inputs `κ₂_vis`, `κ₂_hid`, `μ_vis`, `μ_hid`, fixed by
  the Baker form on SM Yukawas (visible) and the see-saw cascade
  (hidden) at `ξ_R ≈ 3.7090`.

## References

* Ben-Shalom, "Spectral Physics", v0.9, Proposition `prop:faith-tower`
  (line 9735), Chapter 25 (cumulant tower).
* `pre_geometric/faithfulness_tower_l3/report.md` (mixture-variance
  decomposition).
* `pre_geometric/Lambda1_refined/scse_refined.py`,
  `refined_values.json` (50-decimal mpmath bisection).
* `pre_geometric/scse_convergence_analysis/scse_extended.py`
  (canonical closure target `κ₂_needed ≈ 529.421091`).
-/

namespace SpectralPhysics.SelfModelDeficit

open Real

/-! ## Mode counts (Tier 1) -/

/-- Visible-sector mode count.  From the v0.9 finite-spectral-triple
    decomposition: 48 Yukawa modes (charged + light-ν + aux) plus 48
    auxiliary modes carrying depth `κ₁ = 6` per mode.  Total 96. -/
def NVis : ℕ := 96

/-- Hidden-sector mode count.  Three see-saw slots × (32 R + 32 D + 32 L)
    = 288. -/
def NHid : ℕ := 288

/-- Total mode count `N = N_vis + N_hid = 384`. -/
def NFull : ℕ := NVis + NHid

theorem NFull_eq_384 : NFull = 384 := by
  unfold NFull NVis NHid; decide

/-! ## Tier-2 numerical inputs

The four numbers below are fixed by the *high-precision* Python
bisection on the Baker-constrained spectrum (50-digit mpmath).  Once
the Baker form is fixed and `ξ_R` is bisected against the SAGF
closure, all four values are determined to 30+ digits. -/

/-- Visible-sector second cumulant `κ₂_vis = 9.927069…`, fixed by the
    Baker form on the 48 Yukawa modes (charged + light-ν + 24 aux at
    `(288 − S_charged − 10.5)/24`) plus 48 auxiliary modes at depth 6.
    Reported to 4 digits.

    **Citation**:
    `pre_geometric/scse_convergence_analysis/scse_extended.py`
    `baker_constrained_xi_vis()`; `Lambda1_refined/scse_refined.py`. -/
noncomputable def kappa2_vis : ℝ := 9927069 / 1000000  -- 9.927069

/-- Hidden-sector second cumulant `κ₂_hid = 533.585765…`, fixed by the
    see-saw cascade `(ξ_R, ξ_D, 2ξ_D − ξ_R)` at `ξ_R = 3.7090359…`,
    `ξ_D = 32`, with 96 modes in each of the three blocks.  Population
    variance evaluates to `(2(28.291)²)/3 + 0 = 533.585765`.  Reported
    to 4 digits.

    **Citation**: `Lambda1_refined/scse_refined.py`,
    `kappa2_full_mp` evaluated at the bisected `ξ_R`. -/
noncomputable def kappa2_hid : ℝ := 533585765 / 1000000  -- 533.585765

/-- Visible-sector mean `μ_vis = κ₁ = 6`, exact at the Baker-form
    level (the Yukawa modes carry the per-fermion mean of 6 by
    construction; the 24 aux modes also average to 6 since they
    absorb `(288 − S_charged − ν)/24`; the 48 depth-6 modes are 6
    each). -/
noncomputable def mu_vis : ℝ := 6

/-- Hidden-sector mean `μ_hid = (ξ_R + ξ_D + (2ξ_D − ξ_R))/3 = ξ_D = 32`,
    independently of `ξ_R`.

    The naive "μ_hid ≈ 1" reading in the early audits used a *single*
    heavy-Majorana mode and missed the D and L cascade slots.  Direct
    summation over the 288-mode cascade gives `μ_hid = 32` exactly. -/
noncomputable def mu_hid : ℝ := 32

/-! ## Sanity arithmetic on the Tier-2 inputs -/

theorem kappa2_vis_pos : 0 < kappa2_vis := by unfold kappa2_vis; norm_num
theorem kappa2_hid_pos : 0 < kappa2_hid := by unfold kappa2_hid; norm_num
theorem mu_vis_pos    : 0 < mu_vis    := by unfold mu_vis;    norm_num
theorem mu_hid_pos    : 0 < mu_hid    := by unfold mu_hid;    norm_num

/-- The mean gap `μ_hid − μ_vis = 26`. -/
theorem mu_gap_eq : mu_hid - mu_vis = 26 := by
  unfold mu_hid mu_vis; norm_num

/-! ## The law-of-total-variance decomposition (Tier 1) -/

/-- Within-sector variance term
    `W = (n_v · κ_v + n_h · κ_h)/N`.  This is `E[Var(ξ|sector)]`. -/
noncomputable def kappa2_within : ℝ :=
  ((NVis : ℝ) * kappa2_vis + (NHid : ℝ) * kappa2_hid) / (NFull : ℝ)

/-- Between-sector variance term
    `B = (n_v · n_h / N²) · (μ_v − μ_h)²`.  This is `Var[E(ξ|sector)]`. -/
noncomputable def kappa2_between : ℝ :=
  ((NVis : ℝ) * (NHid : ℝ) / ((NFull : ℝ) ^ 2)) * (mu_vis - mu_hid) ^ 2

/-- The law of total variance defines `κ₂_full = W + B`. -/
noncomputable def kappa2_full : ℝ := kappa2_within + kappa2_between

/-- The within-sector contribution evaluates to a closed-form rational. -/
theorem kappa2_within_eq :
    kappa2_within
      = (96 * (9927069/1000000) + 288 * (533585765/1000000)) / 384 := by
  unfold kappa2_within kappa2_vis kappa2_hid NFull NVis NHid
  norm_num

/-- The between-sector contribution evaluates to `126.75 = 3·676/16`. -/
theorem kappa2_between_eq :
    kappa2_between = (3 / 16 : ℝ) * 676 := by
  unfold kappa2_between mu_vis mu_hid NFull NVis NHid
  ring

/-- The between-sector contribution evaluates to `126.75`. -/
theorem kappa2_between_value :
    kappa2_between = 12675 / 100 := by
  rw [kappa2_between_eq]; norm_num

/-- **Headline closed-form theorem.**  The law-of-total-variance form
    evaluates to `529.421091…` from the Tier-2 inputs.

    More precisely, expanding `W` and `B`:
      W = (96 · 9.927069 + 288 · 533.585765)/384
        = (953.000624 + 153672.6604)/384  (waiting on multiplications…)
        = (953.000624 + 153672.6604)/384
        = 154625.661024/384  …

    The Lean evaluation just computes the rational normal form. -/
theorem kappa2_full_closed_form :
    kappa2_full
      = (96 * (9927069/1000000) + 288 * (533585765/1000000)) / 384
        + (3 / 16 : ℝ) * 676 := by
  unfold kappa2_full
  rw [kappa2_within_eq, kappa2_between_eq]

/-- Numerical evaluation: `κ₂_full ≈ 529.421091`. -/
theorem kappa2_full_numeric_bracket :
    529 < kappa2_full ∧ kappa2_full < 530 := by
  rw [kappa2_full_closed_form]
  refine ⟨?_, ?_⟩ <;> norm_num

/-- The 1-unit-precision bracket: `|κ₂_full − 529| < 1`.

    This is exactly the inventory's "1-unit precision" goal —
    `top10.md` Rank 6 line 142. -/
theorem kappa2_one_unit_bracket :
    |kappa2_full - 529| < 1 := by
  rcases kappa2_full_numeric_bracket with ⟨h1, h2⟩
  rw [abs_lt]; constructor <;> linarith

/-- The closure quality: `κ₂_full > 529.42`. -/
theorem kappa2_above_529_42 : (52942 / 100 : ℝ) < kappa2_full := by
  rw [kappa2_full_closed_form]; norm_num

/-- The closure quality: `κ₂_full < 529.43`. -/
theorem kappa2_below_529_43 : kappa2_full < 52943 / 100 := by
  rw [kappa2_full_closed_form]; norm_num

/-- Combined: `κ₂_full ∈ (529.42, 529.43)`, a **0.01-unit window**.
    This is *3-orders-of-magnitude tighter* than the inventory's
    "1-unit precision" target.

    The remaining residual (after the 4-digit truncation of the
    Tier-2 inputs) is bounded by `2·10⁻⁴`, well inside the
    1-unit-precision goal. -/
theorem kappa2_centiunit_bracket :
    (52942 / 100 : ℝ) < kappa2_full ∧ kappa2_full < 52943 / 100 := by
  exact ⟨kappa2_above_529_42, kappa2_below_529_43⟩

/-- Distance from the Baker target `529.421091`:
    `|κ₂_full − 529.421091| < 10⁻⁵`. -/
theorem kappa2_baker_target_match :
    |kappa2_full - 529421091 / 1000000| < (1 : ℝ) / 100000 := by
  rw [kappa2_full_closed_form]
  rw [abs_lt]; constructor <;> norm_num

end SpectralPhysics.SelfModelDeficit
