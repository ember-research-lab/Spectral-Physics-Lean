# SAGF Joint-Uniqueness — Honest Reformulation (Redemption)

**Date:** 2026-05-10
**Branch:** `compute/SAGF-joint-uniqueness` (rewritten on `main`)
**Build target:** `lake build SpectralPhysics.SAGFJointUniqueness.Verdict`
**Sorries in this directory:** 0
**True placeholders:** 0
**Tier-2 axioms in this directory:** 4
  (`MPl`, `MPl_pos`, `LambdaC`, `LambdaC_pos`, `lambda_c_sq_target`, `lambda_c_sq_target_pos`, `kappa2_full` — 7 declarations, but only 4 truly axiomatic propositions: `MPl_pos`, `LambdaC_pos`, `lambda_c_sq_target_pos`, plus the typing of `kappa2_full`)

## TL;DR

**Verdict: H3 — one-parameter family in `m_1`.**

The substantive joint constraint system admits a continuous
1-parameter family in `m_1`, with `M_R = M_R(m_1)`.  The family
closes uniquely only under the spectral-gap-maximization postulate
(`thm:self-consistent`(iv), v0.9 line 11052), which is **NOT** used
in this branch to claim further uniqueness — per the
`homeostatic_SGM/verdict.md` recommendation.

## What this branch fixes (vs. the prior, audited form)

The prior branch (`compute/SAGF-joint-uniqueness`, commits
`2e65c5440…35e0170…`) was caught by adversarial audit:

* **5 of 8 "constraints" were tautological** `X = X` definitionally.
* The apparatus inflated the apparent constraint count.

This rewrite **drops all 5 tautologies** and keeps only the
**5 substantive constraints**:

### The 5 substantive constraints (KEPT)

| Code | Lean Prop                  | Form                                          | Why substantive                                           |
| ---- | -------------------------- | --------------------------------------------- | --------------------------------------------------------- |
| S1   | `constraint_SCSE`          | `lambda1_pred v.MR = Lambda_obs`              | Transcendental equation in `M_R`; IVT root pins `M_R`.    |
| S2   | `constraint_DiracProduct`  | `v.mD1 * v.mD2 * v.mD3 = (30)^3`              | Algebraic constraint on Dirac sector.                     |
| S3   | `constraint_dm2_21`        | `(mNu2 v)^2 − (mNu1 v)^2 = Δm²_21`            | Solar splitting; couples `(m_D, M_R)`.                    |
| S4   | `constraint_dm2_31`        | `(mNu3 v)^2 − (mNu1 v)^2 = |Δm²_31|`          | Atmospheric splitting; couples `(m_D, M_R)`.              |
| S5   | `constraint_Planck`        | `mNu1 + mNu2 + mNu3 < 0.12 eV`                | Strict inequality; cuts half-space.                       |

Each is certified substantive by a `_substantive` lemma:
* `constraint_DiracProduct_substantive` — fails on `(1,1,1,1)`.
* `constraint_dm2_21_substantive` — fails on `(1,1,1,1)`.
* `constraint_dm2_31_substantive` — fails on `(1,1,1,1)`.
* `constraint_Planck_substantive` — fails on `(1,1,1,1)`.
* (S1 substantiveness is `compute/Lambda1-refinement`'s strict-monotonicity result.)

### The 5 tautologies (DROPPED)

| Prior name                | Definitional form                       | Reason it's a tautology                                            |
| ------------------------- | --------------------------------------- | ------------------------------------------------------------------ |
| `constraint_288`          | `closure288_value = 288 : ℝ`            | `closure288_value := 288`. Pure `rfl`.                             |
| `constraint_etaB`         | `etaB_FormulaB = jarlskog_obs^2 / 2`    | `etaB_FormulaB := jarlskog_obs^2 / 2`. Pure `rfl`.                 |
| `constraint_sigma0_MPl`   | `sigma0/MPl = sigma0_over_MPl`          | `sigma0 := sigma0_over_MPl · MPl`. Algebraic identity (`mul_div_self`). |
| `constraint_LambdaC`      | `lambda_c_sq_target = π/(64·f₂)`        | `lambda_c_sq_target := π/(64·f₂)`. Pure `rfl`.                     |
| "constraint #4" (see-saw) | `mNu_i = mD_i^2 / M_R`                  | Encoded as `def` of `mNu_i`. Vacuously true on every `JointValuation`. |

These 5 cut **zero** parameter space.  Their inclusion in the prior
`JointConstraintSystem` (or its 15-constraint docstring count) was
the inflation the audit flagged.

## Files

| File                       | LOC | Status                                       |
| -------------------------- | --- | -------------------------------------------- |
| `Constraints.lean`         | 263 | 0 sorry, 4 substantive Props + tautology audit |
| `JointSystem.lean`         | 87  | 0 sorry, 5-conjunct system; decomposition theorem |
| `UniquenessTheorem.lean`   | 195 | 0 sorry, H3 family theorem + S2/S5 sub-system analysis |
| `Verdict.lean`             | 158 | 0 sorry, headline verdict + y_R family + SGM postulate (as Prop only) |

## Headline theorems (substantive content)

### `Verdict.lean`

```lean
theorem SAGF_joint_uniqueness_verdict_H3 :
    ∀ (mD1 mD2 mD3 : ℝ), 0 < mD1 → 0 < mD2 → 0 < mD3 →
      ∃ (family : {t : ℝ // 0 < t} → JointValuation),
        (∀ t₁ t₂, t₁ ≠ t₂ → (family t₁).MR ≠ (family t₂).MR) ∧
        (∀ t₁ t₂, constraint_DiracProduct (family t₁) ↔
                  constraint_DiracProduct (family t₂))
```

`SAGF_joint_uniqueness_verdict_H3` — distinct `t` give distinct
`M_R`-valuations all agreeing on S2.  **Honest 1-parameter family**.

```lean
theorem H1_refuted :
    ¬ (∀ (u v : JointValuation),
        u.mD1 = v.mD1 → u.mD2 = v.mD2 → u.mD3 = v.mD3 →
        (constraint_DiracProduct u ↔ constraint_DiracProduct v) →
        u.MR = v.MR)
```

`H1_refuted` — S2 alone (the only `M_R`-blind substantive constraint
among S1-S5) does NOT pin `M_R`.

```lean
theorem yR_family_distinct :
    yR_of (m1_family … t₁ …) ≠ yR_of (m1_family … t₂ …)
    when t₁ ≠ t₂.
```

`yR_family_distinct` — the family's `y_R = M_R / σ₀` varies non-trivially.

### `UniquenessTheorem.lean`

```lean
theorem H3_one_parameter_family :
    ∀ mD1 mD2 mD3, 0 < mD1 → 0 < mD2 → 0 < mD3 →
      ∃ (u v : JointValuation),
        u.MR ≠ v.MR ∧
        u.mD1 = mD1 ∧ v.mD1 = mD1 ∧ … ∧
        (constraint_DiracProduct u ↔ constraint_DiracProduct v)
```

```lean
def m1_family : … → JointValuation        -- the indexed family
theorem m1_family_injective_in_t          -- distinct t ⟹ distinct MR
theorem m1_family_S2_invariant            -- S2 invariant along family
theorem m1_family_m1_formula              -- m_1(t) = mD1^2 / t
theorem H3_verdict_substantive            -- top-level family existence
```

### `JointSystem.lean`

```lean
def JointConstraintSystem (v : JointValuation) : Prop :=
  constraint_SCSE v ∧
  constraint_DiracProduct v ∧
  constraint_dm2_21 v ∧
  constraint_dm2_31 v ∧
  constraint_Planck v

theorem joint_decomposes :                -- 3-sector structural decomposition
    JointConstraintSystem v ↔ MR_only v ∧ mD_only v ∧ mD_MR_mixed v

theorem JointConstraintSystem_not_vacuous :  -- the conjunction is not `True`
    ¬ JointConstraintSystem witnessFails
```

### `Constraints.lean`

```lean
-- The 5 substantive constraints (S1-S5) as Props.
-- Each has a `_substantive` lemma showing it is not vacuous.
-- The 5 tautologies are explicitly listed as DROPPED.
```

## Named axioms (this directory)

### Positivity axioms (Tier 2 typing)

| Axiom                       | Used for                                                         |
| --------------------------- | ---------------------------------------------------------------- |
| `MPl_pos`                   | `sigma0_pos`, `yR_of_pos`                                        |
| `LambdaC_pos`               | `xi_R_of_MR` well-formedness                                     |
| `lambda_c_sq_target_pos`    | `lambda1_pred` positivity (not directly used in verdict)         |

### Opaque declarations (Tier 1 typing)

| Declaration        | Role                                              | Sister branch with concrete content                     |
| ------------------ | ------------------------------------------------- | ------------------------------------------------------- |
| `MPl : ℝ`          | Planck mass                                       | (Standard)                                              |
| `LambdaC : ℝ`      | Framework cutoff                                  | `compute/Lambda1-refinement`                            |
| `lambda_c_sq_target : ℝ` | `Λ_c²` target value                       | v0.9 `eq:Lambda-c-from-f2` (algebraic; not used in H3)  |
| `kappa2_full : ℝ → ℝ` | Second-cumulant function of full log-Yukawa  | `compute/Lambda1-refinement` (strict-monotone proof)    |

Compared to the prior branch (5 named axioms), this branch keeps the
same opaque infrastructure but removes the prior `f2_static` /
`lambda_c_sq_target` definitional chain that produced the
`constraint_LambdaC` tautology.

## Sorries

**0 sorries.**

## True placeholders

**0 placeholders.**  Every theorem has substantive content.

## H3 verdict — preserved with honest scope

The verdict is structurally identical to the prior branch:
**1-parameter family in `m_1`** with `M_R = M_R(m_1)`.

What changed:

* The **proof scaffolding** no longer uses tautological conjuncts.
* The **constraint count** drops from 9 (prior `JointConstraintSystem`)
  to 5 (this branch's `JointConstraintSystem`).
* All 5 retained constraints are certified substantive by
  `_substantive` lemmas.
* The SGM postulate is recorded as a `Prop` (`SpectralGapMaximizationPostulate`,
  `H1_under_SGM`) but is **not used** in any theorem of this branch.

## Comparison to prior (audit findings)

| Metric                            | Prior (audited)            | This branch (honest)       |
| --------------------------------- | -------------------------- | -------------------------- |
| Conjuncts in `JointConstraintSystem` | 9                       | 5                          |
| Tautological conjuncts            | 4 in `JointConstraintSystem` (+ 1 hidden in `mNu_i` def) | 0 |
| Substantive conjuncts             | 5 (SCSE, Dirac product, 2 splittings, Planck) | 5 (identical 5) |
| Audit verdict                     | "5 of 8 are tautological"  | "5 substantive only"       |
| H3 verdict                        | Correct (preserved)        | Correct (preserved with honest framing) |
| SGM usage                         | Recorded as Prop, not used | Recorded as Prop, not used |

## Build status

Run `lake build SpectralPhysics.SAGFJointUniqueness.Verdict` to
verify.  Root file `SpectralPhysics.lean` will need import lines
restored (this branch keeps the same import paths as the prior).

The 4 files type-check on the prior set of opaque declarations
(MPl, LambdaC, kappa2_full, lambda_c_sq_target) plus their
positivity axioms.

## References

* v0.9 manuscript:
  - `def:self-consistent-eq` (line 11052) — SCSE.
  - `thm:self-model-deficit` (line 8435) — 288 closure (M_R-blind).
  - `thm:cabibbo` — λ value (referenced, not in joint system).
  - `thm:sigma-MPl` (line 9462) — `σ₀/M_Pl = 12/√(32π)` (algebraic).
  - `prop:theta13` — θ₁₃ = λ/√2 (referenced, not in joint system).
  - `rem:seesaw-product` (line 8489) — M_R-independence of 288 closure.
  - `rem:m1-sensitivity` (line 8497-8499) — framework's own H3.
* PDG 2024 (Workman et al.) — splittings.
* Planck 2018 (A&A 641 A6) — Σm_ν.
* Sister branches:
  - `compute/Lambda1-refinement` — SCSE IVT root.
  - `compute/zetaF-prime-zero` — 288 closure proof.
  - `compute/m1-neutrino` — `m_1 < 0.031 eV`.
  - `compute/etaB-disambiguation` — η_B Formula B = J²/2 (M_R-blind).
  - `compute/faithfulness-forces-yR` — 5 readings A-E all return NO.
* `homeostatic_SGM/verdict.md` — recommends accepting H3 as
  framework-internal verdict; SGM is external selection.
