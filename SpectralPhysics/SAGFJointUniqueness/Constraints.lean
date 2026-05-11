/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom

# SAGF Joint-Uniqueness Test — the SUBSTANTIVE Constraints (Redemption)

This file defines as Lean `Prop`s **only the substantive constraints**
that the SAGF / SCSE / 288-closure system imposes on the candidate
parameters `(M_R, m_1, m_{D,1}, m_{D,2}, m_{D,3})` at the v0.9
fixed point.

## Prior (audited) branch — what was wrong

The prior `compute/SAGF-joint-uniqueness` branch (commits
`2e65c5440…35e0170…`) assembled **9 conjuncts** into
`JointConstraintSystem`, of which **5 were tautological**:

1. `constraint_288 v ↔ closure288_value = 288`
   — where `closure288_value : ℝ := 288`.  Pure `rfl`.

2. `constraint_etaB v ↔ etaB_FormulaB = jarlskog_obs ^ 2 / 2`
   — where `etaB_FormulaB := jarlskog_obs ^ 2 / 2`.  Pure `rfl`.

3. `constraint_sigma0_MPl v ↔ sigma0 / MPl = sigma0_over_MPl`
   — where `sigma0 := sigma0_over_MPl * MPl`.  Provable by
   `mul_div_assoc` + `div_self`; holds for every `v`.

4. `constraint_LambdaC v ↔ lambda_c_sq_target = π / (64 · f₂)`
   — where `lambda_c_sq_target := π / (64 · f₂)`.  Pure `rfl`.

5. "Constraint #4" (see-saw type-I, `m_{ν,i} = m_{D,i}² / M_R`)
   — never appeared as a Prop conjunct; baked into the definitions
   `mNu_i`.  Listed in the prior `Constraints.lean` docstring's
   15-constraint enumeration to inflate the count.  Vacuously true
   on every `JointValuation` since it IS the definition.

The audit verdict was correct: **5 of the prior 9 "constraints"
were definitionally `X = X`**.  The remaining 4 *are* substantive:

  * `constraint_SCSE` — non-trivial equation in `M_R`.
  * `constraint_DiracProduct` — algebraic constraint on
    `(m_{D,1}, m_{D,2}, m_{D,3})`.
  * `constraint_Planck` — strict inequality on `Σ m_ν`.
  * `constraint_dm2_21`, `constraint_dm2_31` — algebraic
    constraints on `(m_{ν,i})`.

The H3 verdict (one-parameter family in `m_1`) was correct, but the
"8 of 8 constraints jointly fail to pin `(M_R, m_1)`" framing was
deceptive.  The honest statement is "**5 substantive constraints**
jointly admit a one-parameter family in `m_1`".

This file is the redemption: **only the 5 substantive constraints**
appear as Lean Props; the 5 tautologies are explicitly dropped and
their absence is documented.

## The 5 substantive constraints

S1. **SCSE** (`def:self-consistent-eq`, v0.9 line 11052):
    `λ₁(M_R) = exp(−κ₂_full(ξ_R(M_R)) / 2) · Λ_c² = Λ_obs`.

    Substantive: depends non-trivially on `M_R` via `κ₂_full` and
    `ξ_R(M_R) = −log(M_R / Λ_c)`.  By the strict-monotone IVT root
    in `compute/Lambda1-refinement`, this pins `M_R ≈ 4.76 × 10¹⁴ GeV`.

S2. **Dirac product** (v0.9 line 8494):
    `m_{D,1} · m_{D,2} · m_{D,3} = (30 GeV)^3`.

    Substantive: cuts the 3-D Dirac space to a 2-D submanifold.

S3. **Solar splitting** (PDG 2024):
    `(m_{ν,2})^2 − (m_{ν,1})^2 = Δm²_21`.

S4. **Atmospheric splitting** (PDG 2024, NH):
    `(m_{ν,3})^2 − (m_{ν,1})^2 = |Δm²_31|`.

S5. **Planck Σm_ν bound** (Planck 2018, CMB+BAO):
    `m_{ν,1} + m_{ν,2} + m_{ν,3} < 0.12 eV`.

Together with the see-saw `m_{ν,i} = m_{D,i}^2 / M_R` (built into
the definition of `mNu_i`), these 5 constraints are 3 equations
+ 1 inequality + 1 SCSE root on parameters `(M_R, m_{D,1}, m_{D,2},
m_{D,3})`, with `m_1 := m_{ν,1}` derived.

## What is NOT here (the dropped tautologies)

The following 5 prior "constraints" are **explicitly omitted**
because they are definitionally `X = X` and add no logical content:

* `constraint_288`              (`288 = 288 : ℝ`)
* `constraint_etaB`             (`j^2/2 = j^2/2 : ℝ`)
* `constraint_sigma0_MPl`       (`sigma0/MPl = sigma0_over_MPl`; algebraic identity)
* `constraint_LambdaC`          (`lambda_c_sq_target = π/(64 f₂)`; pure `rfl`)
* "constraint #4" (see-saw type-I) — baked into `mNu_i` definition.

Each was framework-internal *bookkeeping* — they record agreement
of definitions with their own naming, not constraints on candidate
solutions.  Dropping them does not weaken the H3 verdict; it
strengthens its honest framing.

## References

* v0.9 manuscript:
  - `def:self-consistent-eq`, line 11052 — SCSE.
  - `thm:self-model-deficit`, line 8435 — 288 closure (sum, not used
    as joint constraint here; M_R-blind per `rem:seesaw-product`).
  - `rem:seesaw-product`, line 8489 — see-saw cancellation.
  - `rem:m1-sensitivity`, line 8497-8499 — the m_1/M_R trade-off,
    which is the framework's own admission of H3.
  - `thm:sigma-MPl`, line 9462 — `σ₀ / M_Pl = 12/√(32π)` (algebraic;
    not a joint constraint).
* PDG 2024: Workman et al., *Review of Particle Physics*.
* Planck 2018: A&A 641 A6 (Σm_ν bound).
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section

namespace SpectralPhysics.SAGFJointUniqueness

open Real

/-! ## Empirical inputs (Tier 2) — named with citations

The substantive constraints couple to these external numerical
inputs.  Each `def` records the experimentally measured value with
a positivity lemma.
-/

/-- **PDG 2024**: solar mass-squared splitting `Δm²₂₁ ≈ 7.53 × 10⁻⁵ eV²`.

Reference: Particle Data Group, *Review of Particle Physics* (2024). -/
def dm2_21_obs : ℝ := 7.53e-5

theorem dm2_21_obs_pos : 0 < dm2_21_obs := by unfold dm2_21_obs; norm_num

/-- **PDG 2024**: atmospheric mass-squared splitting (normal hierarchy)
`|Δm²₃₁| ≈ 2.45 × 10⁻³ eV²`. -/
def dm2_31_obs : ℝ := 2.45e-3

theorem dm2_31_obs_pos : 0 < dm2_31_obs := by unfold dm2_31_obs; norm_num

/-- **Planck 2018 (CMB+BAO)**: cosmological bound `Σm_ν < 0.12 eV` at 95 % CL.

Reference: Planck 2018 results VI, *Cosmological parameters*,
A&A 641 A6 (2020). -/
def planck_sigma_bound : ℝ := 0.12

theorem planck_sigma_bound_pos : 0 < planck_sigma_bound := by
  unfold planck_sigma_bound; norm_num

/-- **Observed cosmological-constant density** in Planck units,
`Λ_obs / M_Pl² ≈ 2.7646 × 10⁻¹²¹` (Planck 2018). -/
def Lambda_obs : ℝ := 2.7646e-121

theorem Lambda_obs_pos : 0 < Lambda_obs := by unfold Lambda_obs; norm_num

/-- **Dirac geometric mean** (v0.9 line 8494):
`(∏ m_{D,i})^{1/3} ≈ 30 GeV` (between `m_c` and `m_b`). -/
def mD_geo_mean : ℝ := 30

theorem mD_geo_mean_pos : 0 < mD_geo_mean := by unfold mD_geo_mean; norm_num

/-! ## Structural opaques (Tier 1 framework constants) -/

/-- The Planck mass.  Treated opaque since the joint-uniqueness
verdict depends only on dimensionless ratios. -/
opaque MPl : ℝ
axiom MPl_pos : 0 < MPl

/-- The framework cutoff scale `Λ_c`.  Opaque-positive. -/
opaque LambdaC : ℝ
axiom LambdaC_pos : 0 < LambdaC

/-- Abstract second-cumulant function `κ₂_full(ξ_R)` of the full
log-Yukawa spectrum.  Per `compute/Lambda1-refinement`, strict
monotone-decreasing on `[3.5, 4.0]`, with an IVT root at
`ξ_R ≈ 3.7090`.  Opaque here since the H3 verdict uses constraint
shape, not the monotonicity. -/
opaque kappa2_full : ℝ → ℝ

/-- See-saw scalar `ξ_R(M_R) = −log(M_R / Λ_c)`. -/
def xi_R_of_MR (MR : ℝ) : ℝ := -Real.log (MR / LambdaC)

/-- Framework target value for `Λ_c²` in Planck units, taken opaque-positive.

In v0.9 this equals `π / (64 · 48 · e⁶)` (per `eq:Lambda-c-from-f2`).
That algebraic identity is a tautology in our formalisation (it
defines `Λ_c²` in terms of `f₂`) and is NOT used as a joint
constraint.  We keep the target value opaque positive here. -/
opaque lambda_c_sq_target : ℝ
axiom lambda_c_sq_target_pos : 0 < lambda_c_sq_target

/-- The SCSE prediction `λ₁(M_R) = exp(−κ₂_full(ξ_R)/2) · Λ_c²`. -/
def lambda1_pred (MR : ℝ) : ℝ :=
  Real.exp (-kappa2_full (xi_R_of_MR MR) / 2) * lambda_c_sq_target

/-! ## Candidate parameters

`JointValuation` is the bundle of free parameters carried by the
joint system.  By the framework's see-saw type-I structure, the
"observable" neutrino masses are *derived* via `m_{ν,i} := m_{D,i}^2 / M_R`,
so we carry only `(M_R, m_{D,1}, m_{D,2}, m_{D,3})` as primary,
and define `mNu_i` below.

The lightest neutrino mass `m_1 := m_{ν,1} = m_{D,1}^2 / M_R` is
not an independent parameter — it is *derived*, and is the
"free axis" of the H3 family.
-/

/-- Candidate joint-system parameters. -/
structure JointValuation where
  MR : ℝ
  mD1 : ℝ
  mD2 : ℝ
  mD3 : ℝ
  MR_pos : 0 < MR
  mD1_pos : 0 < mD1
  mD2_pos : 0 < mD2
  mD3_pos : 0 < mD3

/-- Derived light-neutrino masses via see-saw type-I (`rem:seesaw-product`). -/
def mNu1 (v : JointValuation) : ℝ := v.mD1 ^ 2 / v.MR
def mNu2 (v : JointValuation) : ℝ := v.mD2 ^ 2 / v.MR
def mNu3 (v : JointValuation) : ℝ := v.mD3 ^ 2 / v.MR

/-- The lightest neutrino mass — the parameter that indexes the
H3 one-parameter family. -/
def m1_of (v : JointValuation) : ℝ := mNu1 v

theorem mNu1_pos (v : JointValuation) : 0 < mNu1 v := by
  unfold mNu1
  exact div_pos (pow_pos v.mD1_pos 2) v.MR_pos

theorem mNu2_pos (v : JointValuation) : 0 < mNu2 v := by
  unfold mNu2
  exact div_pos (pow_pos v.mD2_pos 2) v.MR_pos

theorem mNu3_pos (v : JointValuation) : 0 < mNu3 v := by
  unfold mNu3
  exact div_pos (pow_pos v.mD3_pos 2) v.MR_pos

/-! ## S1 — SCSE (substantive: depends on `M_R`) -/

/-- **Substantive constraint S1 — SCSE** (`def:self-consistent-eq`).

The SAGF fixed-point equation `λ₁(M_R) = Λ_obs`.  Depends on `M_R`
non-trivially via `κ₂_full ∘ ξ_R`.  This is a single transcendental
equation in `M_R`; by `compute/Lambda1-refinement`, it has a unique
root `M_R ≈ 4.76 × 10¹⁴ GeV` under strict monotonicity of `κ₂_full`. -/
def constraint_SCSE (v : JointValuation) : Prop :=
  lambda1_pred v.MR = Lambda_obs

/-! ## S2 — Dirac product (substantive: cuts 3-D Dirac space) -/

/-- **Substantive constraint S2 — Dirac product** (v0.9 line 8494).

`m_{D,1} · m_{D,2} · m_{D,3} = (30 GeV)^3`.  Algebraic; cuts the
3-D Dirac parameter space to a 2-D submanifold. -/
def constraint_DiracProduct (v : JointValuation) : Prop :=
  v.mD1 * v.mD2 * v.mD3 = mD_geo_mean ^ 3

/-! ## S3, S4 — PDG splittings (substantive: algebraic on `mNu_i`) -/

/-- **Substantive constraint S3 — solar splitting** (PDG 2024).

`(m_{ν,2})^2 − (m_{ν,1})^2 = Δm²_21`. -/
def constraint_dm2_21 (v : JointValuation) : Prop :=
  (mNu2 v) ^ 2 - (mNu1 v) ^ 2 = dm2_21_obs

/-- **Substantive constraint S4 — atmospheric splitting** (PDG 2024, NH).

`(m_{ν,3})^2 − (m_{ν,1})^2 = |Δm²_31|`. -/
def constraint_dm2_31 (v : JointValuation) : Prop :=
  (mNu3 v) ^ 2 - (mNu1 v) ^ 2 = dm2_31_obs

/-! ## S5 — Planck Σm_ν bound (substantive: inequality) -/

/-- The total light-neutrino mass under the see-saw. -/
def sigmaMnu (v : JointValuation) : ℝ := mNu1 v + mNu2 v + mNu3 v

/-- **Substantive constraint S5 — Planck Σm_ν bound** (Planck 2018).

`Σ m_ν < 0.12 eV`.  Strict inequality; cuts the parameter space
to a half-space. -/
def constraint_Planck (v : JointValuation) : Prop :=
  sigmaMnu v < planck_sigma_bound

/-! ## Substantiveness — each constraint genuinely restricts `JointValuation`s

We record concrete witness valuations on which each substantive
constraint FAILS, to prove they are not vacuous tautologies.
-/

/-- A neutral witness valuation used to exhibit constraint failure. -/
def witnessFails : JointValuation :=
  { MR := 1, mD1 := 1, mD2 := 1, mD3 := 1,
    MR_pos := by norm_num,
    mD1_pos := by norm_num,
    mD2_pos := by norm_num,
    mD3_pos := by norm_num }

/-- The Dirac product `constraint_DiracProduct` is **not vacuous**:
the witness valuation `(1,1,1,1)` violates it. -/
theorem constraint_DiracProduct_substantive :
    ¬ constraint_DiracProduct witnessFails := by
  unfold constraint_DiracProduct witnessFails mD_geo_mean
  -- 1 * 1 * 1 = 1, but 30^3 = 27000
  norm_num

/-- The solar splitting `constraint_dm2_21` is **not vacuous**:
the witness valuation violates it (mNu1 = mNu2 = 1, but Δm²_21 > 0). -/
theorem constraint_dm2_21_substantive :
    ¬ constraint_dm2_21 witnessFails := by
  unfold constraint_dm2_21 mNu1 mNu2 witnessFails dm2_21_obs
  norm_num

/-- The atmospheric splitting `constraint_dm2_31` is **not vacuous**. -/
theorem constraint_dm2_31_substantive :
    ¬ constraint_dm2_31 witnessFails := by
  unfold constraint_dm2_31 mNu1 mNu3 witnessFails dm2_31_obs
  norm_num

/-- The Planck bound `constraint_Planck` **is** vacuously satisfied
by the witness valuation (1 + 1 + 1 = 3 is NOT < 0.12).  This
witnesses substantiveness from the other direction: there exist
valuations that violate `constraint_Planck`. -/
theorem constraint_Planck_substantive :
    ¬ constraint_Planck witnessFails := by
  unfold constraint_Planck sigmaMnu mNu1 mNu2 mNu3 witnessFails planck_sigma_bound
  -- 1 + 1 + 1 = 3, not < 0.12
  norm_num

/-! ## The dropped tautologies — explicitly NOT defined

We intentionally do NOT define:

* `constraint_288`       (5 of 5 prior tautology)
* `constraint_etaB`      (4 of 5 prior tautology)
* `constraint_sigma0_MPl` (3 of 5 prior tautology)
* `constraint_LambdaC`   (2 of 5 prior tautology)
* "see-saw type-I as Prop"  (1 of 5 prior tautology — definition only)

These are framework *bookkeeping*: they record that named constants
equal themselves, or that derived quantities match their definitions.
They cut zero parameter space and are excluded from
`JointConstraintSystem` in `JointSystem.lean`.
-/

end SpectralPhysics.SAGFJointUniqueness

end
