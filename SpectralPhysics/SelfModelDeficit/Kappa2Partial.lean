/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import SpectralPhysics.SelfModelDeficit.Kappa2

/-!
# `κ₂Partial` — a mode-resolved, truncatable second cumulant, and the
  `A_s = P · exp(−κ₂ᶦⁿᶠ/2)` assembly

This file implements `spec:as-partial-cumulant`.  It builds the
*machine* — a per-mode population variance `kappa2Partial` — and the
`A_s` assembly + transfer function.  It deliberately does **NOT** decide
the inflation-epoch mode set, and it does **NOT** close `A_s`.

## What this file proves (T1, zero `sorry`, zero new `axiom`)

* **Task 1 (machine + tests).** A genuine population-variance functional
  `pvar v S = (1/|S|) Σ_{i∈S}(v i − mean_S v)²`, instantiated on the
  visible-fermion index `VisFermion` with its per-mode log-Yukawa
  `negLogY` (the index `ι` *already used* for the visible-sector
  distribution — not a new one).  The required spec tests:
  - `kappa2Partial ∅ = 0`,
  - `kappa2Partial {a} = 0` (variance of one point).

* **Task 1 (hidden cascade — where per-mode data EXISTS).** The hidden
  see-saw cascade `(ξ_R, ξ_D, 2ξ_D − ξ_R)` IS genuinely mode-resolvable
  in closed form: its equal-weight population variance reduces to
  `2(ξ_D − ξ_R)²/3`, independently of multiplicity.  At the documented
  `ξ_R = 3.7090359, ξ_D = 32` this reproduces `κ₂_hid = 533.586` to
  `< 10⁻⁵`.

* **Task 1 (the honest negative — where per-mode data is ABSENT).** The
  full-spectrum anchor `kappa2Partial univ = 529.42` is **NOT**
  reconstructible from the per-mode data the Lean repo contains.  The
  visible Yukawa coupling `y : VisFermion → ℝ` is an opaque `axiom`
  (only PDG-cited *per-sector* sums `S_up, …` and the *aggregate*
  `κ₂_vis = 9.927069` exist; the individual `−log y_f` do not).  We
  PROVE the divergence as a theorem (`RIGOROUS_WORKFLOW.md` Rule 6):
  the data genuinely in the repo (hidden cascade variance + between-
  sector term + visible modes at their mean) reconstructs `526.94`; the
  remaining `2.48 = (N_vis/N)·κ₂_vis` is the within-visible spread, an
  aggregate input with no per-mode grounding in the repo.

* **Task 2 (`A_s` assembly).** `AsValue P S = P · exp(−κ₂Partial(S)/2)`,
  with `P` an INPUT (two-valued: `P₁ = 1.03·10⁻²` for `c₁ = 1`,
  `P₂ = 1.58·10⁻⁴` for `c₁ = λ_σ`).  We verify that at the FULL cumulant
  `κ₂ = 529.42`, `A_s = P·exp(−264.71)` is CC-scale (vanishing) — which
  is exactly *why* `A_s` needs a PARTIAL cumulant.

* **Task 3 (transfer function + honest report).** Standalone
  `AsTransfer P κ = P · exp(−κ/2)`.  The full table is in
  `results/as_transfer.md`.  Here we Lean-bracket the band-matching
  `κ₂ᶦⁿᶠ` for each prefactor:
  - `c₁ = 1`  (`P₁`):  `A_s ∈ [1.9, 2.3]·10⁻⁹`  for  `κ₂ᶦⁿᶠ ∈ (30, 32)`,
  - `c₁ = λ_σ` (`P₂`): `A_s ∈ [1.9, 2.3]·10⁻⁹`  for  `κ₂ᶦⁿᶠ ∈ (22, 24)`.
  These bracket the spec's expected `≈ 22–31` range.  The mode set that
  realises such a `κ₂ᶦⁿᶠ` is a physics judgment NOT decided here.

## References

* `spec:as-partial-cumulant` (Spec-Queue).
* `Kappa2.lean` (`kappa2_full`, `kappa2_vis`, `kappa2_hid`, `mu_*`).
* `Yukawas.lean` (`negLogY`, the opaque `axiom y`, per-sector sums).
* `RIGOROUS_WORKFLOW.md` Rule 6 / Phase 4 (honest negatives as theorems).
-/

namespace SpectralPhysics.SelfModelDeficit

open Real Finset

/-! ## Task 1a — the population-variance machine (generic, then on `ι = VisFermion`) -/

/-- Sample mean of `v` over the finite mode set `S`. -/
noncomputable def meanOver {ι : Type*} (v : ι → ℝ) (S : Finset ι) : ℝ :=
  (∑ i ∈ S, v i) / S.card

/-- **The machine.**  Population variance of `v` over the mode set `S`:
    `(1/|S|) Σ_{i∈S} (v i − mean_S v)²`.  Truncatable by construction —
    `S` ranges over arbitrary `Finset`s of the mode index. -/
noncomputable def pvar {ι : Type*} (v : ι → ℝ) (S : Finset ι) : ℝ :=
  (∑ i ∈ S, (v i - meanOver v S) ^ 2) / S.card

/-- Variance over the empty mode set is `0`. -/
theorem pvar_empty {ι : Type*} (v : ι → ℝ) : pvar v ∅ = 0 := by
  simp [pvar]

/-- Variance over a singleton is `0` (the spread of one point is zero). -/
theorem pvar_singleton {ι : Type*} (v : ι → ℝ) (a : ι) : pvar v {a} = 0 := by
  simp [pvar, meanOver]

/-- **`kappa2Partial`** — the mode-resolved cumulant on the index `ι`
    *already used* for the visible-sector distribution (`VisFermion`),
    with the per-fermion log-Yukawa `negLogY` from `Yukawas.lean`. -/
noncomputable def kappa2Partial (S : Finset VisFermion) : ℝ := pvar negLogY S

/-- Spec test: `kappa2Partial` of the empty set `= 0`. -/
theorem kappa2Partial_empty : kappa2Partial ∅ = 0 := pvar_empty _

/-- Spec test: `kappa2Partial` of any singleton `= 0`. -/
theorem kappa2Partial_singleton (a : VisFermion) : kappa2Partial {a} = 0 :=
  pvar_singleton _ _

/-! ## Task 1b — the hidden see-saw cascade IS mode-resolvable in closed form

The hidden sector's 288 modes are `96` copies each of the three see-saw
slots `(ξ_R, ξ_D, 2ξ_D − ξ_R)` (`Kappa2.lean` docstring, lines 36–40).
Equal multiplicities ⇒ the 288-mode population variance equals the
3-point population variance.  We prove the closed form and that it
reproduces the aggregate `κ₂_hid`. -/

/-- Mean of the equal-weight 3-point cascade `(a, m, 2m − a)`. -/
noncomputable def cascadeMean (a m : ℝ) : ℝ := (a + m + (2 * m - a)) / 3

/-- Population variance of the equal-weight 3-point cascade `(a, m, 2m − a)`. -/
noncomputable def cascadeVar (a m : ℝ) : ℝ :=
  ((a - m) ^ 2 + (m - m) ^ 2 + ((2 * m - a) - m) ^ 2) / 3

/-- The cascade mean is `m`, independently of `a` (this is `μ_hid = ξ_D`). -/
theorem cascadeMean_eq (a m : ℝ) : cascadeMean a m = m := by
  unfold cascadeMean; ring

/-- **Closed form.**  The cascade variance is `2(m − a)²/3`.  Because the
    three slots carry equal multiplicity, the full 288-mode variance is
    identical — the hidden sector is genuinely mode-resolved. -/
theorem cascadeVar_eq (a m : ℝ) : cascadeVar a m = 2 * (m - a) ^ 2 / 3 := by
  unfold cascadeVar; ring

/-- The bisected heavy-Majorana depth `ξ_R = 3.7090359` (`Kappa2.lean`
    docstring line 118; `SeeSawCancel.lean`).  A repo-grounded constant,
    not a free parameter. -/
noncomputable def xiR : ℝ := 37090359 / 10000000

/-- The Dirac depth `ξ_D = 32` (`Kappa2.lean` docstring line 39). -/
noncomputable def xiD : ℝ := 32

/-- **Hidden reconstruction CONVERGES.**  The per-mode cascade variance at
    the documented `(ξ_R, ξ_D)` reproduces the aggregate `κ₂_hid` to
    `< 10⁻⁵` — the hidden sector's aggregate input *is* grounded in its
    per-mode structure. -/
theorem cascadeVar_reproduces_kappa2_hid :
    |cascadeVar xiR xiD - kappa2_hid| < 1 / 100000 := by
  rw [cascadeVar_eq]
  unfold xiR xiD kappa2_hid
  rw [abs_lt]; constructor <;> norm_num

/-! ## Task 1c — the honest negative: the full-spectrum anchor is NOT
    reconstructible from repo per-mode data

`kappa2_full = 529.42` decomposes (law of total variance, `Kappa2.lean`)
into within-visible `(N_vis/N)·κ₂_vis`, within-hidden `(N_hid/N)·κ₂_hid`,
and between `B`.  The hidden within-term is mode-grounded (§1b above);
the between-term `B` uses only the sector means (`μ_vis = 6`, `μ_hid = 32`,
both repo constants).  The within-visible term `(N_vis/N)·κ₂_vis` is the
ONLY piece requiring per-mode visible data — and that data is absent
(`y : VisFermion → ℝ` is an opaque `axiom`; only per-sector sums exist).
We quantify exactly the resulting shortfall. -/

/-- The within-visible spread contribution to `κ₂_full`,
    `(N_vis/N)·κ₂_vis`.  This is the piece with NO per-mode grounding. -/
noncomputable def kappa2_visible_spread : ℝ :=
  (NVis : ℝ) / (NFull : ℝ) * kappa2_vis

theorem kappa2_visible_spread_eq :
    kappa2_visible_spread = (96 / 384) * (9927069 / 1000000) := by
  unfold kappa2_visible_spread kappa2_vis NFull NVis NHid
  push_cast; norm_num

/-- The within-visible spread is `≈ 2.482`. -/
theorem kappa2_visible_spread_bracket :
    (248 / 100 : ℝ) < kappa2_visible_spread ∧ kappa2_visible_spread < 249 / 100 := by
  rw [kappa2_visible_spread_eq]; constructor <;> norm_num

/-- The cumulant reconstructed from the per-mode data the repo ACTUALLY
    contains: the hidden cascade variance `(N_hid/N)·κ₂_hid` (§1b,
    mode-grounded), the between-sector term `B` (from the two sector
    means), and the visible modes placed AT their mean (zero within-
    visible spread, because the individual visible `−log y_f` are not in
    the repo). -/
noncomputable def kappa2_modeGrounded : ℝ :=
  (NHid : ℝ) / (NFull : ℝ) * kappa2_hid + kappa2_between

/-- **The divergence, as an identity.**  `κ₂_full` exceeds the mode-
    grounded reconstruction by EXACTLY the within-visible spread. -/
theorem kappa2_full_minus_modeGrounded :
    kappa2_full - kappa2_modeGrounded = kappa2_visible_spread := by
  unfold kappa2_full kappa2_within kappa2_modeGrounded kappa2_visible_spread
  unfold NVis NHid NFull
  push_cast
  ring

/-- **The honest negative (headline).**  The per-mode reconstruction
    grounded in genuine repo data reaches only `≈ 526.94` of the
    aggregate `κ₂_full = 529.42`.  The shortfall of `≈ 2.48` is the
    within-visible-Yukawa spread `κ₂_vis = 9.927069`, an aggregate
    Tier-2 input whose individual per-mode `−log y_f` values are NOT
    present in the Lean repo.  Per `spec` Success-Criterion 7, we do not
    force the anchor — we report exactly where it diverges. -/
theorem kappa2_modeGrounded_bracket :
    (52693 / 100 : ℝ) < kappa2_modeGrounded ∧ kappa2_modeGrounded < 52695 / 100 := by
  unfold kappa2_modeGrounded kappa2_between kappa2_hid mu_vis mu_hid NFull NVis NHid
  push_cast
  constructor <;> norm_num

/-! ## Task 2 — the `A_s` assembly -/

/-- **Task 3 standalone transfer function** `A_s(κ, P) = P · exp(−κ/2)`. -/
noncomputable def AsTransfer (P kappa : ℝ) : ℝ := P * Real.exp (-(kappa / 2))

/-- **Task 2 assembly** `A_s = P · exp(−κ₂Partial(S)/2)`. `P` is an INPUT. -/
noncomputable def AsValue (P : ℝ) (S : Finset VisFermion) : ℝ :=
  AsTransfer P (kappa2Partial S)

/-- Trace-sector prefactor for `c₁ = 1`:  `P₁ = 1.03·10⁻²` (an INPUT). -/
noncomputable def P_c1_one : ℝ := 103 / 10000

/-- Trace-sector prefactor for `c₁ = λ_σ ≈ 0.124`:  `P₂ = 1.58·10⁻⁴`
    (an INPUT). -/
noncomputable def P_c1_lamSig : ℝ := 158 / 1000000

/-- `AsTransfer` is positive when `P > 0`. -/
theorem AsTransfer_pos {P : ℝ} (hP : 0 < P) (kappa : ℝ) : 0 < AsTransfer P kappa := by
  unfold AsTransfer; exact mul_pos hP (Real.exp_pos _)

/-- **`A_s` at the FULL cumulant is CC-scale (vanishing).**  With
    `κ₂ = 529.42`, `A_s = P₁·exp(−264.71)`, so `log A_s < −250` (i.e.
    `A_s ≲ 10⁻¹¹⁶`).  This is *why* `A_s` requires a PARTIAL cumulant:
    the full cumulant over-suppresses by ~100 orders.  The partial/full
    distinction is real (contrast the band-matching `κ₂ᶦⁿᶠ ≈ 22–31`
    below). -/
theorem AsValue_full_is_CC_scale :
    Real.log (AsTransfer P_c1_one kappa2_full) < -250 := by
  unfold AsTransfer P_c1_one
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  have h2 : (52942 / 100 : ℝ) < kappa2_full := kappa2_above_529_42
  have hlog : Real.log (103 / 10000) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  linarith

/-! ## Task 3 — band-matching `κ₂ᶦⁿᶠ` brackets (spot-checks of the transfer table)

Planck band: `A_s ∈ [1.9, 2.3]·10⁻⁹`, i.e. `[19, 23]·10⁻¹⁰`.
We bracket the band-matching `κ₂ᶦⁿᶠ` for each prefactor by exhibiting an
`A_s` above the band and an `A_s` below it (so the crossing lies between).

`exp` bounds via Mathlib's `Real.exp_one_{gt,lt}_d9`, following
`F4Coefficient.lean`'s idiom. -/

theorem exp_11_lt : Real.exp 11 < 60500 := by
  have h_e : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hexp : Real.exp 11 = (Real.exp 1) ^ 11 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [hexp]
  have h_pos : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos _).le
  have h_pow : (Real.exp 1) ^ 11 ≤ (2.7182818286 : ℝ) ^ 11 :=
    pow_le_pow_left₀ h_pos h_e.le 11
  have h_num : (2.7182818286 : ℝ) ^ 11 < 60500 := by norm_num
  linarith

theorem exp_12_gt : (162000 : ℝ) < Real.exp 12 := by
  have h_e : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hexp : Real.exp 12 = (Real.exp 1) ^ 12 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [hexp]
  have h_num : (162000 : ℝ) < (2.7182818283 : ℝ) ^ 12 := by norm_num
  exact lt_of_lt_of_le h_num (pow_le_pow_left₀ (by norm_num) h_e.le 12)

theorem exp_15_lt : Real.exp 15 < 3300000 := by
  have h_e : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hexp : Real.exp 15 = (Real.exp 1) ^ 15 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [hexp]
  have h_pos : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos _).le
  have h_pow : (Real.exp 1) ^ 15 ≤ (2.7182818286 : ℝ) ^ 15 :=
    pow_le_pow_left₀ h_pos h_e.le 15
  have h_num : (2.7182818286 : ℝ) ^ 15 < 3300000 := by norm_num
  linarith

theorem exp_16_gt : (8800000 : ℝ) < Real.exp 16 := by
  have h_e : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hexp : Real.exp 16 = (Real.exp 1) ^ 16 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [hexp]
  have h_num : (8800000 : ℝ) < (2.7182818283 : ℝ) ^ 16 := by norm_num
  exact lt_of_lt_of_le h_num (pow_le_pow_left₀ (by norm_num) h_e.le 16)

/-- `AsTransfer P (2n) = P / exp n` — peels the `/2` off even `κ`. -/
theorem AsTransfer_even (P : ℝ) (n : ℝ) :
    AsTransfer P (2 * n) = P / Real.exp n := by
  unfold AsTransfer
  rw [show -((2 * n) / 2) = -n by ring, Real.exp_neg, div_eq_mul_inv]

/-- `c₁ = 1`: at `κ₂ᶦⁿᶠ = 30`, `A_s = P₁·exp(−15) ≈ 3.15·10⁻⁹` is ABOVE
    the Planck band (`> 2.3·10⁻⁹`). -/
theorem As_P1_kappa30_above_band :
    (23 / 10000000000 : ℝ) < AsTransfer P_c1_one 30 := by
  have key : AsTransfer P_c1_one 30 = P_c1_one / Real.exp 15 := by
    rw [show (30 : ℝ) = 2 * 15 by norm_num, AsTransfer_even]
  rw [key]; unfold P_c1_one
  have h : Real.exp 15 < 3300000 := exp_15_lt
  have hpos : (0 : ℝ) < Real.exp 15 := Real.exp_pos _
  have h2 : (103 / 10000 : ℝ) / 3300000 ≤ (103 / 10000) / Real.exp 15 := by
    gcongr
  have h3 : (23 / 10000000000 : ℝ) < (103 / 10000) / 3300000 := by norm_num
  linarith

/-- `c₁ = 1`: at `κ₂ᶦⁿᶠ = 32`, `A_s = P₁·exp(−16) ≈ 1.16·10⁻⁹` is BELOW
    the Planck band (`< 1.9·10⁻⁹`).  Hence the band-matching `κ₂ᶦⁿᶠ` for
    `c₁ = 1` lies in `(30, 32)`. -/
theorem As_P1_kappa32_below_band :
    AsTransfer P_c1_one 32 < 19 / 10000000000 := by
  have key : AsTransfer P_c1_one 32 = P_c1_one / Real.exp 16 := by
    rw [show (32 : ℝ) = 2 * 16 by norm_num, AsTransfer_even]
  rw [key]; unfold P_c1_one
  have h : (8800000 : ℝ) < Real.exp 16 := exp_16_gt
  have hpos : (0 : ℝ) < Real.exp 16 := Real.exp_pos _
  have h2 : (103 / 10000 : ℝ) / Real.exp 16 ≤ (103 / 10000) / 8800000 := by
    gcongr
  have h3 : (103 / 10000 : ℝ) / 8800000 < 19 / 10000000000 := by norm_num
  linarith

/-- `c₁ = λ_σ`: at `κ₂ᶦⁿᶠ = 22`, `A_s = P₂·exp(−11) ≈ 2.64·10⁻⁹` is ABOVE
    the Planck band (`> 2.3·10⁻⁹`). -/
theorem As_P2_kappa22_above_band :
    (23 / 10000000000 : ℝ) < AsTransfer P_c1_lamSig 22 := by
  have key : AsTransfer P_c1_lamSig 22 = P_c1_lamSig / Real.exp 11 := by
    rw [show (22 : ℝ) = 2 * 11 by norm_num, AsTransfer_even]
  rw [key]; unfold P_c1_lamSig
  have h : Real.exp 11 < 60500 := exp_11_lt
  have hpos : (0 : ℝ) < Real.exp 11 := Real.exp_pos _
  have h2 : (158 / 1000000 : ℝ) / 60500 ≤ (158 / 1000000) / Real.exp 11 := by
    gcongr
  have h3 : (23 / 10000000000 : ℝ) < (158 / 1000000) / 60500 := by norm_num
  linarith

/-- `c₁ = λ_σ`: at `κ₂ᶦⁿᶠ = 24`, `A_s = P₂·exp(−12) ≈ 9.7·10⁻¹⁰` is BELOW
    the Planck band (`< 1.9·10⁻⁹`).  Hence the band-matching `κ₂ᶦⁿᶠ` for
    `c₁ = λ_σ` lies in `(22, 24)`. -/
theorem As_P2_kappa24_below_band :
    AsTransfer P_c1_lamSig 24 < 19 / 10000000000 := by
  have key : AsTransfer P_c1_lamSig 24 = P_c1_lamSig / Real.exp 12 := by
    rw [show (24 : ℝ) = 2 * 12 by norm_num, AsTransfer_even]
  rw [key]; unfold P_c1_lamSig
  have h : (162000 : ℝ) < Real.exp 12 := exp_12_gt
  have hpos : (0 : ℝ) < Real.exp 12 := Real.exp_pos _
  have h2 : (158 / 1000000 : ℝ) / Real.exp 12 ≤ (158 / 1000000) / 162000 := by
    gcongr
  have h3 : (158 / 1000000 : ℝ) / 162000 < 19 / 10000000000 := by norm_num
  linarith

/-- **The transfer-function verdict.**  Both prefactors place the band-
    matching `κ₂ᶦⁿᶠ` inside the spec's expected `≈ 22–31` window:
    `c₁ = λ_σ ⇒ κ₂ᶦⁿᶠ ∈ (22, 24)` and `c₁ = 1 ⇒ κ₂ᶦⁿᶠ ∈ (30, 32)`.
    Which mode set realises such a `κ₂ᶦⁿᶠ` is a physics judgment that is
    a TARGET for an independent derivation, NOT produced here. -/
theorem As_band_matching_kappa_inf :
    (AsTransfer P_c1_lamSig 22 > 23 / 10000000000 ∧
      AsTransfer P_c1_lamSig 24 < 19 / 10000000000) ∧
    (AsTransfer P_c1_one 30 > 23 / 10000000000 ∧
      AsTransfer P_c1_one 32 < 19 / 10000000000) :=
  ⟨⟨As_P2_kappa22_above_band, As_P2_kappa24_below_band⟩,
   ⟨As_P1_kappa30_above_band, As_P1_kappa32_below_band⟩⟩

end SpectralPhysics.SelfModelDeficit
