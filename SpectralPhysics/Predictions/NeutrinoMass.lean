/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Lightest Neutrino Mass `m_1` Bracket from Planck `Σ m_ν < 0.12 eV`

This file pins the lightest neutrino mass `m_1` (in eV) within the
window allowed by:

* PDG mass-squared splittings (normal ordering):
  `Δm²_21 ≈ 7.53 × 10⁻⁵ eV²`,
  `|Δm²_31| ≈ 2.45 × 10⁻³ eV²`.

* Planck (CMB+BAO 2018) cosmological bound:
  `Σ m_ν < 0.12 eV`.

* The framework's see-saw + functional-determinant prediction
  `Σ m_ν ≈ 0.058–0.063 eV` (v0.9, Prediction `pred:neutrino-mass`).

For normal hierarchy:

  `m_2 = √(m_1² + Δm²_21)`,
  `m_3 = √(m_1² + |Δm²_31|)`,
  `Σ m_ν = m_1 + m_2 + m_3`.

`Σ m_ν` is a strictly increasing function of `m_1` (each summand is
non-decreasing, the first summand strictly increasing).  Combined with
the Planck bound, this gives a strict upper bound on `m_1`; the
floor is reached at `m_1 = 0`, giving `Σ m_ν > 0.058 eV`, which
already saturates Planck's lower allowed corner.

## Tier classification

* **Tier 1 (proved here)**: monotonicity, the Planck-window upper
  bound `m_1 < 0.031 eV`, the floor `Σ m_ν > 0.058 eV` at `m_1 = 0`,
  and the v0.9 quoted window `Σ m_ν ∈ [0.058, 0.063]` for
  `m_1 ∈ [0, 0.0035]`.

* **Tier 2 (named axioms / definitions)**: the PDG mass-squared
  splittings and the Planck `Σ m_ν` upper bound — these are external
  experimental inputs.  We state them as `def`s with documented
  citations to make the empirical inputs explicit.

* **Tier 3 (not formalized)**: the see-saw mechanism that would
  derive `m_1` *uniquely* from `M_R` and the Dirac mass scheme.
  The framework does not produce a single value of `m_1`; it
  produces a one-parameter window, exactly as v0.9 Prediction
  `pred:neutrino-mass` quotes.

## Honest framing

This is **not** a first-principles derivation of `m_1`.  It is a
*bracket*: assuming the Planck bound and the PDG splittings, `m_1`
is constrained to a narrow window.  The framework's see-saw
provides a *consistency check* (via `M_R`), not an additional
prediction beyond what oscillation + cosmology already give.

## References

* Ben-Shalom, "Spectral Physics", v0.9, Remark `rem:m1-sensitivity`
  (line 8497–8499) and Prediction `pred:neutrino-mass`.
* Planck Collaboration (2018), *Planck 2018 results. VI.
  Cosmological parameters*, A&A 641, A6.
* Particle Data Group (2024), *Review of Particle Physics*.
-/

noncomputable section

namespace SpectralPhysics.NeutrinoMass

open Real

/-! ## PDG inputs (Tier 2 inputs) -/

/-- **PDG solar mass-squared splitting** (NuFIT/PDG 2024):
    `Δm²_21 ≈ 7.53 × 10⁻⁵ eV²`. -/
def dm2_21 : ℝ := 7.53e-5

/-- **PDG atmospheric mass-squared splitting** (PDG 2024,
    normal hierarchy assumed): `|Δm²_31| ≈ 2.45 × 10⁻³ eV²`. -/
def dm2_31 : ℝ := 2.45e-3

/-- **Planck 2018 cosmological bound** (CMB+BAO):
    `Σ m_ν < 0.12 eV` at 95% CL. -/
def planckBound : ℝ := 0.12

/-! ## Mass functions for normal hierarchy -/

/-- The second neutrino mass: `m_2(m_1) = √(m_1² + Δm²_21)`. -/
def m2 (m1 : ℝ) : ℝ := Real.sqrt (m1 ^ 2 + dm2_21)

/-- The third neutrino mass: `m_3(m_1) = √(m_1² + |Δm²_31|)`. -/
def m3 (m1 : ℝ) : ℝ := Real.sqrt (m1 ^ 2 + dm2_31)

/-- The sum of neutrino masses: `Σ m_ν = m_1 + m_2 + m_3`. -/
def sigmaMnu (m1 : ℝ) : ℝ := m1 + m2 m1 + m3 m1

/-! ## Basic positivity facts -/

theorem dm2_21_pos : 0 < dm2_21 := by unfold dm2_21; norm_num
theorem dm2_31_pos : 0 < dm2_31 := by unfold dm2_31; norm_num

theorem m2_pos (m1 : ℝ) : 0 < m2 m1 := by
  unfold m2
  apply Real.sqrt_pos.mpr
  have h1 : 0 ≤ m1 ^ 2 := sq_nonneg _
  have h2 : 0 < dm2_21 := dm2_21_pos
  linarith

theorem m3_pos (m1 : ℝ) : 0 < m3 m1 := by
  unfold m3
  apply Real.sqrt_pos.mpr
  have h1 : 0 ≤ m1 ^ 2 := sq_nonneg _
  have h2 : 0 < dm2_31 := dm2_31_pos
  linarith

theorem m2_nonneg (m1 : ℝ) : 0 ≤ m2 m1 := le_of_lt (m2_pos m1)
theorem m3_nonneg (m1 : ℝ) : 0 ≤ m3 m1 := le_of_lt (m3_pos m1)

/-! ## Monotonicity -/

theorem m2_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : m2 a ≤ m2 b := by
  unfold m2
  apply Real.sqrt_le_sqrt
  have h : a ^ 2 ≤ b ^ 2 := by nlinarith
  linarith

theorem m3_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : m3 a ≤ m3 b := by
  unfold m3
  apply Real.sqrt_le_sqrt
  have h : a ^ 2 ≤ b ^ 2 := by nlinarith
  linarith

theorem sigmaMnu_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    sigmaMnu a ≤ sigmaMnu b := by
  unfold sigmaMnu
  have h2 := m2_mono ha hab
  have h3 := m3_mono ha hab
  linarith

/-! ## Floor at `m_1 = 0`: the normal-hierarchy minimum

At `m_1 = 0`:
  `m_2 = √(7.53e-5) ≈ 0.008678 eV`,
  `m_3 = √(2.45e-3)  ≈ 0.049497 eV`,
  `Σ ≈ 0.058175 eV` — the well-known NH lower edge.
-/

/-- At `m_1 = 0`, `m_2 = √Δm²_21 > 0.00867`. -/
theorem m2_at_zero_lower : (0.00867 : ℝ) < m2 0 := by
  unfold m2 dm2_21
  have step : (0.00867 : ℝ) = Real.sqrt (0.00867 ^ 2) :=
    (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 0.00867)).symm
  rw [step]
  apply Real.sqrt_lt_sqrt
  · positivity
  · norm_num

/-- At `m_1 = 0`, `m_3 = √|Δm²_31| > 0.04949`. -/
theorem m3_at_zero_lower : (0.04949 : ℝ) < m3 0 := by
  unfold m3 dm2_31
  have step : (0.04949 : ℝ) = Real.sqrt (0.04949 ^ 2) :=
    (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 0.04949)).symm
  rw [step]
  apply Real.sqrt_lt_sqrt
  · positivity
  · norm_num

/-- **`sigmaMnu` floor**: even at `m_1 = 0`, `Σ m_ν > 0.058 eV` —
    the normal-hierarchy minimum, saturated only at vanishing
    lightest mass. -/
theorem sigmaMnu_floor : (0.058 : ℝ) < sigmaMnu 0 := by
  unfold sigmaMnu
  have h2 := m2_at_zero_lower
  have h3 := m3_at_zero_lower
  -- sigmaMnu 0 = 0 + m2 0 + m3 0 > 0.00867 + 0.04949 = 0.05816
  -- and 0.058 < 0.05816 holds.  Direct linarith.
  linarith

/-! ## Upper-side bounds at `m_1 = 0` -/

/-- At `m_1 = 0`, `m_2 = √Δm²_21 < 0.00868`. -/
theorem m2_at_zero_upper : m2 0 < (0.00868 : ℝ) := by
  unfold m2 dm2_21
  have step : (0.00868 : ℝ) = Real.sqrt (0.00868 ^ 2) :=
    (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 0.00868)).symm
  rw [step]
  apply Real.sqrt_lt_sqrt
  · positivity
  · norm_num

/-- At `m_1 = 0`, `m_3 = √|Δm²_31| < 0.04950`. -/
theorem m3_at_zero_upper : m3 0 < (0.04950 : ℝ) := by
  unfold m3 dm2_31
  have step : (0.04950 : ℝ) = Real.sqrt (0.04950 ^ 2) :=
    (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 0.04950)).symm
  rw [step]
  apply Real.sqrt_lt_sqrt
  · positivity
  · norm_num

/-- At `m_1 = 0`, `Σ m_ν < 0.05819 eV`. -/
theorem sigmaMnu_at_zero_upper : sigmaMnu 0 < (0.05819 : ℝ) := by
  unfold sigmaMnu
  have h2 := m2_at_zero_upper
  have h3 := m3_at_zero_upper
  -- sigmaMnu 0 = 0 + m2 0 + m3 0 < 0.00868 + 0.04950 = 0.05818 < 0.05819 ✓
  linarith

/-! ## Upper bound for `m_1`: Planck window

We show that at `m_1 = 0.031`, `Σ m_ν > 0.12 = planckBound`.
By monotonicity, `Σ m_ν < planckBound` forces `m_1 < 0.031`.

Numerical sanity at `m_1 = 0.031`:
  `m_1² = 9.61 × 10⁻⁴`,
  `m_2 = √(9.61e-4 + 7.53e-5) = √(1.0363e-3) ≈ 0.03219`,
  `m_3 = √(9.61e-4 + 2.45e-3) = √(3.411e-3)  ≈ 0.05841`,
  `Σ ≈ 0.031 + 0.03219 + 0.05841 = 0.1216 > 0.12` ✓
-/

/-- At `m_1 = 0.031`, `m_2 > 0.0321`. -/
theorem m2_at_031_lower : (0.0321 : ℝ) < m2 0.031 := by
  unfold m2 dm2_21
  have step : (0.0321 : ℝ) = Real.sqrt (0.0321 ^ 2) :=
    (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 0.0321)).symm
  rw [step]
  apply Real.sqrt_lt_sqrt
  · positivity
  · norm_num

/-- At `m_1 = 0.031`, `m_3 > 0.0584`. -/
theorem m3_at_031_lower : (0.0584 : ℝ) < m3 0.031 := by
  unfold m3 dm2_31
  have step : (0.0584 : ℝ) = Real.sqrt (0.0584 ^ 2) :=
    (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 0.0584)).symm
  rw [step]
  apply Real.sqrt_lt_sqrt
  · positivity
  · norm_num

/-- At `m_1 = 0.031`, `Σ m_ν > 0.12`. -/
theorem sigmaMnu_exceeds_planck_at_031 : planckBound < sigmaMnu 0.031 := by
  unfold sigmaMnu planckBound
  have h2 := m2_at_031_lower
  have h3 := m3_at_031_lower
  -- 0.031 + 0.0321 + 0.0584 = 0.1215 > 0.12 ✓
  linarith

/-- **m_1 upper bound**: if `Σ m_ν` respects Planck's `< 0.12 eV`
    bound, then `m_1 < 0.031 eV`.

    Contrapositive of monotonicity: at `m_1 ≥ 0.031`,
    `Σ m_ν ≥ sigmaMnu 0.031 > 0.12 = planckBound`. -/
theorem m1_upper_bound (m1 : ℝ) (_h_nn : 0 ≤ m1)
    (h_planck : sigmaMnu m1 < planckBound) :
    m1 < 0.031 := by
  by_contra h
  push_neg at h  -- h : 0.031 ≤ m1
  have hmono : sigmaMnu 0.031 ≤ sigmaMnu m1 :=
    sigmaMnu_mono (by norm_num) h
  have hexc : planckBound < sigmaMnu 0.031 :=
    sigmaMnu_exceeds_planck_at_031
  linarith

/-! ## Lower bound for `m_1`: the v0.9 sweep window

The v0.9 remark states `m_1 ∈ [10⁻⁴, 10⁻²] eV`, which corresponds
to the see-saw acceptance window.  We prove the lower-edge bound:
the v0.9 sweep starts at `m_1 = 10⁻⁴`, so under the v0.9 framework
`m_1 > 10⁻⁵` (loose) — this is honest documentation: there is no
*lower* bound from cosmology alone (one can take `m_1 → 0`).
-/

/-- **m_1 lower bound** (v0.9 sweep range, Tier 2 documentation).

    The v0.9 `rem:m1-sensitivity` quotes the sensitivity sweep over
    `m_1 ∈ [10⁻⁴, 10⁻²] eV`.  *Within that sweep* the lower edge is
    `m_1 = 10⁻⁴`; we record this as a *parameter-window*
    statement, not as a bound derived from physics.

    Note: there is no rigorous *lower* bound on `m_1` from cosmology
    alone; the floor `Σ m_ν ≥ 0.058 eV` (NH minimum) is reached at
    `m_1 → 0`.  See `sigmaMnu_floor`. -/
theorem m1_lower_bound (m1 : ℝ) (hsweep : (1e-4 : ℝ) ≤ m1) :
    (1e-5 : ℝ) < m1 := by
  -- 1e-5 < 1e-4 ≤ m1
  have : (1e-5 : ℝ) < (1e-4 : ℝ) := by norm_num
  linarith

/-! ## Σm_ν in the v0.9 window `[0.058, 0.063]`

We verify the v0.9-quoted window: for `m_1 ∈ [0, 0.0035]`,
`Σ m_ν ∈ [0.058, 0.063]`.

Numerical sanity at `m_1 = 0.0035`:
  `m_1² = 1.225e-5`,
  `m_2 = √(1.225e-5 + 7.53e-5) = √(8.755e-5) ≈ 0.009357`,
  `m_3 = √(1.225e-5 + 2.45e-3) = √(2.46225e-3) ≈ 0.04962`,
  `Σ ≈ 0.0035 + 0.009357 + 0.04962 = 0.06248 < 0.063` ✓
-/

/-- At `m_1 = 0.0035`, `m_2 < 0.00936`. -/
theorem m2_at_0035_upper : m2 0.0035 < (0.00936 : ℝ) := by
  unfold m2 dm2_21
  have step : (0.00936 : ℝ) = Real.sqrt (0.00936 ^ 2) :=
    (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 0.00936)).symm
  rw [step]
  apply Real.sqrt_lt_sqrt
  · positivity
  · norm_num

/-- At `m_1 = 0.0035`, `m_3 < 0.04963`. -/
theorem m3_at_0035_upper : m3 0.0035 < (0.04963 : ℝ) := by
  unfold m3 dm2_31
  have step : (0.04963 : ℝ) = Real.sqrt (0.04963 ^ 2) :=
    (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 0.04963)).symm
  rw [step]
  apply Real.sqrt_lt_sqrt
  · positivity
  · norm_num

/-- At `m_1 = 0.0035`, `Σ m_ν < 0.063`. -/
theorem sigmaMnu_at_0035_upper : sigmaMnu 0.0035 < (0.063 : ℝ) := by
  unfold sigmaMnu
  have h2 := m2_at_0035_upper
  have h3 := m3_at_0035_upper
  -- 0.0035 + 0.00936 + 0.04963 = 0.06249 < 0.063 ✓
  linarith

/-- **v0.9 window — upper edge**: for `0 ≤ m_1 ≤ 0.0035`,
    `Σ m_ν ≤ 0.063`. -/
theorem sigmaMnu_in_v09_upper (m1 : ℝ) (h_nn : 0 ≤ m1)
    (h_le : m1 ≤ 0.0035) :
    sigmaMnu m1 < 0.063 := by
  have hmono : sigmaMnu m1 ≤ sigmaMnu 0.0035 := sigmaMnu_mono h_nn h_le
  have hupper : sigmaMnu 0.0035 < (0.063 : ℝ) := sigmaMnu_at_0035_upper
  linarith

/-- **v0.9 window — lower edge**: for `0 ≤ m_1`, `Σ m_ν ≥ 0.058`
    (strict at `m_1 = 0`, loose for `m_1 > 0`). -/
theorem sigmaMnu_in_v09_lower (m1 : ℝ) (h_nn : 0 ≤ m1) :
    (0.058 : ℝ) ≤ sigmaMnu m1 := by
  have hmono : sigmaMnu 0 ≤ sigmaMnu m1 := sigmaMnu_mono le_rfl h_nn
  have hfloor : (0.058 : ℝ) < sigmaMnu 0 := sigmaMnu_floor
  linarith

/-- **Headline theorem — `Σ m_ν` lies in the v0.9 window**.

    For `m_1 ∈ [0, 0.0035]`, `0.058 ≤ Σ m_ν ≤ 0.063`.

    This matches v0.9 Prediction `pred:neutrino-mass`:
    `Σ m_ν ≈ 0.058–0.063 eV`. -/
theorem sigma_m_nu_in_window (m1 : ℝ)
    (h_nn : 0 ≤ m1) (h_le : m1 ≤ 0.0035) :
    (0.058 : ℝ) ≤ sigmaMnu m1 ∧ sigmaMnu m1 ≤ (0.063 : ℝ) := by
  refine ⟨sigmaMnu_in_v09_lower m1 h_nn, ?_⟩
  have h := sigmaMnu_in_v09_upper m1 h_nn h_le
  linarith

/-! ## Falsifiable prediction (Tier 1 documentation)

`Σ m_ν ∈ [0.058, 0.063] eV` is the framework's prediction.  CMB-S4
(`σ(Σm_ν) ≈ 0.02 eV`) and Euclid (`σ(Σm_ν) ≈ 0.03 eV`) will probe
this window within a decade.  A measured value `Σ m_ν > 0.063 eV`
(at, say, 3σ) would falsify the see-saw + functional-determinant
identity — i.e., would force a reading where `m_1 > 0.0035 eV` and
hence `M_R` outside its v0.9 acceptance window.
-/

/-- **Falsifiability statement (informational).**

    Writing the prediction as a strict bracket: there is `m_1*` (the
    framework's lightest-mass parameter) with `0 ≤ m_1* ≤ 0.0035`
    such that `Σ m_ν ∈ [0.058, 0.063]`.  The contrapositive is the
    falsifier: if `Σ m_ν > 0.063` (and is consistent with NH
    splittings), then `m_1* > 0.0035`. -/
theorem framework_prediction :
    ∃ m1 : ℝ, 0 ≤ m1 ∧ m1 ≤ 0.0035 ∧
      (0.058 : ℝ) ≤ sigmaMnu m1 ∧ sigmaMnu m1 ≤ 0.063 := by
  refine ⟨0, le_rfl, by norm_num, ?_, ?_⟩
  · exact sigmaMnu_in_v09_lower 0 le_rfl
  · have h := sigmaMnu_in_v09_upper 0 le_rfl (by norm_num)
    linarith

end SpectralPhysics.NeutrinoMass

end
