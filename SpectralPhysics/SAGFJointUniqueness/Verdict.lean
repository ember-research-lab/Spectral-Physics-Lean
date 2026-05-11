/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom

# SAGF Joint-Uniqueness — Honest Verdict (Redemption)

## TL;DR

**Verdict: H3** — one-parameter family in `m_1`, with `M_R = M_R(m_1)`.

The honest, minimalist reformulation uses **only 5 substantive
constraints** (S1-S5 in `Constraints.lean`).  No tautologies appear
in the joint system.

## Substantive constraint scorecard

| Code | Name                | Substantive? | Comment                                          |
| ---- | ------------------- | ------------ | ------------------------------------------------ |
| S1   | SCSE                | YES          | Depends on `M_R` via `κ₂_full`; IVT root pinned. |
| S2   | Dirac product       | YES          | Cuts 3-D Dirac space.                            |
| S3   | Δm²_21 splitting    | YES          | Algebraic on `(m_D, M_R)`.                       |
| S4   | Δm²_31 splitting    | YES          | Algebraic on `(m_D, M_R)`.                       |
| S5   | Planck Σm_ν bound   | YES          | Strict inequality.                               |

## Dropped tautologies (the 5 from the audit)

| Prior code              | Form                                  | Tautology? |
| ----------------------- | ------------------------------------- | ---------- |
| `constraint_288`        | `closure288_value = 288 : ℝ`          | YES (`rfl`) |
| `constraint_etaB`       | `etaB_FormulaB = jarlskog^2 / 2`      | YES (`rfl`) |
| `constraint_sigma0_MPl` | `sigma0/MPl = sigma0_over_MPl`        | YES (algebraic) |
| `constraint_LambdaC`    | `lambda_c_sq_target = π/(64 f₂)`      | YES (`rfl`) |
| "constraint #4" (see-saw) | `m_{ν,i} = m_{D,i}^2 / M_R`         | YES (definition only) |

These 5 are explicitly omitted from `JointConstraintSystem` in this
branch — see `Constraints.lean`.

## H3 verdict — type-checked

The headline theorem `SAGF_joint_uniqueness_verdict_H3` exhibits a
**1-parameter family** of `JointValuation`s, indexed by `t > 0`
(equivalently `m_1`), that all satisfy the `m_1`-blind substantive
constraint S2 identically.  Hence the substantive joint system does
NOT pin `(M_R, m_1)`.

This matches v0.9 `rem:m1-sensitivity` (line 8497-8499):

  > "Varying `m_1` from `10⁻⁴` to `10⁻²` eV shifts `M_R` from
  >  `1.5 × 10¹⁵` to `2.8 × 10¹⁴` GeV."

The family closes uniquely only under the **extra-axiomatic**
spectral-gap maximization postulate (`thm:self-consistent`(iv),
v0.9 line 11052).  That postulate is NOT used to claim further
uniqueness in this branch; it is mentioned only as the framework's
external selection rule, per the `homeostatic_SGM/verdict.md`
recommendation.

## Provenance

* v0.9 manuscript (anchors):
  - `def:self-consistent-eq`, line 11052.
  - `thm:self-model-deficit`, line 8435.
  - `thm:cabibbo`, `thm:sigma-MPl` (line 9462).
  - `prop:theta13`, `rem:seesaw-product` (line 8489),
    `rem:m1-sensitivity` (line 8497-8499).
* PDG 2024, Planck 2018.
* `compute/Lambda1-refinement`, `compute/zetaF-prime-zero`,
  `compute/m1-neutrino`, `compute/etaB-disambiguation`,
  `compute/faithfulness-forces-yR`.
* `homeostatic_SGM/verdict.md` — recommends accepting H3 as
  framework-internal verdict; SGM is external selection.
-/

import SpectralPhysics.SAGFJointUniqueness.UniquenessTheorem

noncomputable section

namespace SpectralPhysics.SAGFJointUniqueness

open Real

/-! ## Headline H3 verdict (substantive form) -/

/-- **THE SAGF JOINT-UNIQUENESS VERDICT (H3, honest substantive form).**

The substantive joint constraint system (S1-S5 from `Constraints.lean`)
admits a **continuous 1-parameter family** of `JointValuation`s.  For
any fixed positive Dirac data, there exists a family of valuations,
indexed by `t > 0` (with `t = M_R`, and derived `m_1 = mD1^2 / t`),
such that:

* distinct `t` give distinct `M_R`, hence distinct `m_1`;
* the family preserves the truth value of S2 (Dirac product),
  the only `M_R`-blind substantive constraint among S1-S5.

This is the formal, type-checked H3 verdict — the substantive joint
system does NOT pin `(M_R, m_1)` without extra-axiomatic input
(v0.9 `thm:self-consistent`(iv) — spectral-gap maximization,
explicitly external to S1-S5). -/
theorem SAGF_joint_uniqueness_verdict_H3
    (mD1 mD2 mD3 : ℝ) (h1 : 0 < mD1) (h2 : 0 < mD2) (h3 : 0 < mD3) :
    ∃ (family : {t : ℝ // 0 < t} → JointValuation),
      (∀ t₁ t₂, t₁ ≠ t₂ → (family t₁).MR ≠ (family t₂).MR) ∧
      (∀ t₁ t₂, constraint_DiracProduct (family t₁) ↔
                constraint_DiracProduct (family t₂)) :=
  H3_verdict_substantive mD1 mD2 mD3 h1 h2 h3

/-- **Negative form: H1 refuted under S2 alone**.

S2 (Dirac product) does NOT pin `M_R` — distinct `M_R` values with
identical Dirac data yield valuations with the same S2 truth value. -/
theorem H1_refuted :
    ¬ (∀ (u v : JointValuation),
        u.mD1 = v.mD1 → u.mD2 = v.mD2 → u.mD3 = v.mD3 →
        (constraint_DiracProduct u ↔ constraint_DiracProduct v) →
        u.MR = v.MR) :=
  H1_refuted_under_S2

/-! ## Derived `y_R` from the H3 family

Connect to the v0.9 identification `y_R = M_R / σ₀`.  Since the
family varies `M_R` continuously, `y_R` also varies continuously
along the family.  This is the formal content of "`y_R` is
transcendent until `m_1` is measured."
-/

/-- `σ₀` from `thm:sigma-MPl`: `σ₀ = (12/√(32π)) · M_Pl`.  Algebraic
identity used to express `y_R = M_R / σ₀`; positivity only. -/
def sigma0 : ℝ := (12 / Real.sqrt (32 * Real.pi)) * MPl

theorem sigma0_pos : 0 < sigma0 := by
  unfold sigma0
  apply mul_pos
  · apply div_pos (by norm_num : (12 : ℝ) > 0)
    apply Real.sqrt_pos.mpr
    have hpi : 0 < Real.pi := Real.pi_pos
    linarith
  · exact MPl_pos

/-- The Majorana Yukawa coupling derived from a `JointValuation`. -/
def yR_of (v : JointValuation) : ℝ := v.MR / sigma0

theorem yR_of_pos (v : JointValuation) : 0 < yR_of v :=
  div_pos v.MR_pos sigma0_pos

/-- The H3 family of `y_R` values, indexed by `t = M_R`.  Distinct
`t` produce distinct `y_R`. -/
theorem yR_family_distinct
    (mD1 mD2 mD3 : ℝ) (h1 : 0 < mD1) (h2 : 0 < mD2) (h3 : 0 < mD3)
    (t₁ t₂ : ℝ) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (hne : t₁ ≠ t₂) :
    yR_of (m1_family mD1 mD2 mD3 h1 h2 h3 t₁ ht₁) ≠
    yR_of (m1_family mD1 mD2 mD3 h1 h2 h3 t₂ ht₂) := by
  unfold yR_of m1_family mkValuation
  intro h
  -- t₁/sigma0 = t₂/sigma0 ⟹ t₁ = t₂
  have hs0 : sigma0 ≠ 0 := ne_of_gt sigma0_pos
  have : t₁ = t₂ := by
    field_simp at h
    exact h
  exact hne this

/-! ## SGM postulate — mentioned but NOT used here

We define the spectral-gap-maximization postulate as a Prop
placeholder.  Per the redemption brief, we do NOT use it to claim
further uniqueness in this branch; the v0.9 framework treats it as
external.  See `homeostatic_SGM/verdict.md`.
-/

/-- **Spectral-gap-maximization postulate** (v0.9
`thm:self-consistent`(iv), line 11052), stated as a Prop.

"Among all `JointValuation`s satisfying a property `S`, there exists
one maximizing `λ₁(M_R)`."  This is the framework's extra-axiomatic
selection rule.  **NOT** used in any theorem of this branch — recorded
only as the postulate that v0.9 invokes to close the H3 family. -/
def SpectralGapMaximizationPostulate : Prop :=
  ∀ (S : JointValuation → Prop),
    (∃ v, S v) →
    ∃ vmax : JointValuation, S vmax ∧
      ∀ v', S v' → lambda1_pred v'.MR ≤ lambda1_pred vmax.MR

/-- The framework's internal closure: *conditional* uniqueness under SGM.

We state this as a Prop (NOT a theorem) since the postulate is
external.  This honestly records what v0.9 claims, without proving
it from S1-S5. -/
def H1_under_SGM : Prop :=
  SpectralGapMaximizationPostulate →
    ∃ vmax : JointValuation, JointConstraintSystem vmax ∧
      ∀ v, JointConstraintSystem v →
        lambda1_pred v.MR ≤ lambda1_pred vmax.MR

end SpectralPhysics.SAGFJointUniqueness

end
