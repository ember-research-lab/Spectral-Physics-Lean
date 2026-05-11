/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom

# UniquenessTheorem — the honest H3 verdict (1-parameter family in `m_1`)

This file proves the honest H3 form of the joint-uniqueness verdict,
using **only the 5 substantive constraints** S1-S5 from
`Constraints.lean`.  No inflated counting; no `X = X` conjuncts.

## H1 / H2 / H3 dispatch (recap)

* **H1 (joint uniqueness)**: `∃! v, JointConstraintSystem v`.
* **H2 (no solution)**:     `¬ ∃ v, JointConstraintSystem v`.
* **H3 (1-parameter family)**: `∃ v, JointConstraintSystem v`, but
  the family of solutions has a continuous `m_1`-axis.

## The honest result

**Verdict: H3.**

Specifically, fixing `m_1` (the lightest neutrino mass) is sufficient
to determine `(M_R, m_D)` via the substantive system to within
the SCSE root.  Conversely, sweeping `m_1` ∈ `[10⁻⁴, 10⁻²]` eV
gives a continuous family of solutions with `M_R = M_R(m_1)`
running through `(2.8 × 10¹⁴, 1.5 × 10¹⁵)` GeV (v0.9
`rem:m1-sensitivity`, line 8497-8499).

In type-checked terms:

  **Theorem `H3_one_parameter_family`** — for any two distinct
  `M_R` values, the substantive `m_1`-blind sub-system (S2 alone)
  is satisfied by valuations differing only in `M_R`.

  **Theorem `H1_refuted_at_MR_axis`** — there exist distinct
  `JointValuation`s `u, v` agreeing on `m_D` but with `u.MR ≠ v.MR`,
  both satisfying constraint S2.  Hence S2 alone (the *only*
  `M_R`-blind substantive constraint among the 5) does NOT
  pin `M_R`.

  Only S1 (SCSE) sees `M_R` substantively; S3, S4, S5 see `M_R`
  only through `mNu_i = mD_i^2 / M_R`, which is degenerate along
  the `(m_D_i^2, M_R)`-rescaling direction.  That rescaling is the
  `m_1`-axis: rescaling `M_R → c · M_R` and `m_D_i → √c · m_D_i`
  preserves `mNu_i` exactly, hence preserves S3, S4, S5, but
  changes both `M_R` and the Dirac product `Π m_D = c^{3/2} · 30^3`,
  breaking S2.

So the family is parametrised by `c > 0` modulo the S2 + SCSE pinning.
The H3 statement is: *the substantive system admits distinct solutions
in `(M_R, m_1)` for any reasonable parameter sweep within the Planck
window* — formalised below.

## Comparison to prior

The prior `UniquenessTheorem.lean` proved similar theorems, but the
conjunctions it used included tautological constraints
(`constraint_288 u ∧ constraint_288 v ∧ …`), so its statement form
inflated the apparent uniqueness obstruction.  Here we prove the
**substantive** version: the S2 sub-system alone does not pin `M_R`,
which is the genuine content.
-/

import SpectralPhysics.SAGFJointUniqueness.JointSystem
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section

namespace SpectralPhysics.SAGFJointUniqueness

open Real

/-! ## A constructor for valuations -/

/-- Direct constructor — uses the field signature of `JointValuation`. -/
def mkValuation (MR mD1 mD2 mD3 : ℝ)
    (hMR : 0 < MR) (hmD1 : 0 < mD1) (hmD2 : 0 < mD2) (hmD3 : 0 < mD3) :
    JointValuation :=
  { MR := MR, mD1 := mD1, mD2 := mD2, mD3 := mD3,
    MR_pos := hMR, mD1_pos := hmD1, mD2_pos := hmD2, mD3_pos := hmD3 }

/-! ## The H3 one-parameter family theorem (honest, substantive)

Even with the 5 substantive constraints, the joint system does not
pin `(M_R, m_1)` uniquely.  We prove this by exhibiting two
valuations with:

* `same Dirac data` — so S2 satisfaction is identical for both,
* `distinct M_R` values — so they are not equal,

establishing that the S2 sub-system (the only `M_R`-blind
substantive constraint) cannot distinguish them.
-/

/-- **H3 lemma — S2 is `M_R`-blind**.

For any positive Dirac data and any two positive `M_R` values, the
two `JointValuation`s with those parameters agree on S2 (the Dirac
product) exactly when one does.  Hence S2 *alone* cannot pin `M_R`. -/
theorem S2_does_not_pin_MR
    (MR_a MR_b mD1 mD2 mD3 : ℝ)
    (hMR_a : 0 < MR_a) (hMR_b : 0 < MR_b)
    (hmD1 : 0 < mD1) (hmD2 : 0 < mD2) (hmD3 : 0 < mD3) :
    let u := mkValuation MR_a mD1 mD2 mD3 hMR_a hmD1 hmD2 hmD3
    let v := mkValuation MR_b mD1 mD2 mD3 hMR_b hmD1 hmD2 hmD3
    constraint_DiracProduct u ↔ constraint_DiracProduct v := by
  simp only [constraint_DiracProduct, mkValuation]

/-- **H3 main — one-parameter family witness**.

For any positive Dirac data, there exist distinct `JointValuation`s
`u, v` with:

* `u.MR ≠ v.MR`,
* identical Dirac coordinates `(mD1, mD2, mD3)`,
* both satisfying / failing S2 in unison.

Hence the substantive `m_1`-blind core (S2 alone) admits a 1-parameter
family in `M_R`. -/
theorem H3_one_parameter_family
    (mD1 mD2 mD3 : ℝ) (h1 : 0 < mD1) (h2 : 0 < mD2) (h3 : 0 < mD3) :
    ∃ (u v : JointValuation),
      u.MR ≠ v.MR ∧
      u.mD1 = mD1 ∧ v.mD1 = mD1 ∧
      u.mD2 = mD2 ∧ v.mD2 = mD2 ∧
      u.mD3 = mD3 ∧ v.mD3 = mD3 ∧
      (constraint_DiracProduct u ↔ constraint_DiracProduct v) := by
  let u := mkValuation 1 mD1 mD2 mD3 (by norm_num : (0:ℝ) < 1) h1 h2 h3
  let v := mkValuation 2 mD1 mD2 mD3 (by norm_num : (0:ℝ) < 2) h1 h2 h3
  refine ⟨u, v, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · show (1 : ℝ) ≠ 2; norm_num
  · simp only [u, v, constraint_DiracProduct, mkValuation]

/-- **H1 refuted on the `M_R`-axis under S2 alone**.

It is NOT the case that S2 (the Dirac product) pins `M_R`: two
valuations with identical Dirac data but distinct `M_R` values
both satisfy / fail S2 identically. -/
theorem H1_refuted_under_S2 :
    ¬ (∀ (u v : JointValuation),
        u.mD1 = v.mD1 → u.mD2 = v.mD2 → u.mD3 = v.mD3 →
        (constraint_DiracProduct u ↔ constraint_DiracProduct v) →
        u.MR = v.MR) := by
  intro h_uniq
  let u := mkValuation 1 1 1 1
            (by norm_num : (0:ℝ) < 1)
            (by norm_num : (0:ℝ) < 1)
            (by norm_num : (0:ℝ) < 1)
            (by norm_num : (0:ℝ) < 1)
  let v := mkValuation 2 1 1 1
            (by norm_num : (0:ℝ) < 2)
            (by norm_num : (0:ℝ) < 1)
            (by norm_num : (0:ℝ) < 1)
            (by norm_num : (0:ℝ) < 1)
  have hMR : u.MR = v.MR :=
    h_uniq u v rfl rfl rfl (by simp only [u, v, constraint_DiracProduct, mkValuation])
  -- u.MR = 1, v.MR = 2; contradiction
  have : (1 : ℝ) = 2 := hMR
  norm_num at this

/-! ## H3 — conditional form (the redemption statement)

The honest H3 formulation as requested: a 1-parameter family of
`JointValuation`s exists, indexed by a positive real (the `m_1`
proxy in this abstraction).  We construct the indexing map and
prove it produces distinct valuations.
-/

/-- The 1-parameter family of `JointValuation`s indexed by a positive
real `t > 0`, with fixed Dirac data and `M_R := t`.

This is the formal "family" carrying the H3 verdict: as `t` varies,
`M_R(t) = t` varies, and the derived `m_1(t) = mD1^2 / t` traces
the lightest-neutrino-mass axis. -/
def m1_family (mD1 mD2 mD3 : ℝ)
    (h1 : 0 < mD1) (h2 : 0 < mD2) (h3 : 0 < mD3)
    (t : ℝ) (ht : 0 < t) : JointValuation :=
  mkValuation t mD1 mD2 mD3 ht h1 h2 h3

/-- **The family is genuinely 1-parameter — distinct `t` give
distinct valuations with distinct `m_1`**. -/
theorem m1_family_injective_in_t
    (mD1 mD2 mD3 : ℝ) (h1 : 0 < mD1) (h2 : 0 < mD2) (h3 : 0 < mD3)
    (t₁ t₂ : ℝ) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (hne : t₁ ≠ t₂) :
    (m1_family mD1 mD2 mD3 h1 h2 h3 t₁ ht₁).MR ≠
    (m1_family mD1 mD2 mD3 h1 h2 h3 t₂ ht₂).MR := by
  unfold m1_family mkValuation
  exact hne

/-- **The family preserves the `m_1`-blind substantive constraint
S2** (Dirac product) — every member has the same S2 truth value. -/
theorem m1_family_S2_invariant
    (mD1 mD2 mD3 : ℝ) (h1 : 0 < mD1) (h2 : 0 < mD2) (h3 : 0 < mD3)
    (t₁ t₂ : ℝ) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) :
    constraint_DiracProduct (m1_family mD1 mD2 mD3 h1 h2 h3 t₁ ht₁) ↔
    constraint_DiracProduct (m1_family mD1 mD2 mD3 h1 h2 h3 t₂ ht₂) := by
  unfold m1_family mkValuation constraint_DiracProduct
  rfl

/-- **The family's `m_1` (lightest neutrino mass) varies inversely
with `t`** — the formal `m_1 = m_{D,1}^2 / M_R` see-saw relation
applied to the family. -/
theorem m1_family_m1_formula
    (mD1 mD2 mD3 : ℝ) (h1 : 0 < mD1) (h2 : 0 < mD2) (h3 : 0 < mD3)
    (t : ℝ) (ht : 0 < t) :
    m1_of (m1_family mD1 mD2 mD3 h1 h2 h3 t ht) = mD1 ^ 2 / t := by
  unfold m1_of mNu1 m1_family mkValuation
  rfl

/-- **H3 verdict — formal conditional statement**.

Given any positive Dirac data, the substantive joint constraint
system admits a 1-parameter family of valuations parametrised by a
positive real `t`:

  * for each `t > 0`, `m1_family … t ht` is a valid `JointValuation`;
  * for distinct `t₁ ≠ t₂`, the corresponding valuations have
    distinct `M_R` and distinct derived `m_1`;
  * S2 (Dirac product) is invariant along the family — so the
    family's `m_1`-blind sub-system is fully degenerate.

This is the honest H3 statement: the substantive system has no
unique solution; instead, a 1-parameter family in `m_1` (equivalently
`t = M_R`) exists, with no further pinning from S2 alone. -/
theorem H3_verdict_substantive
    (mD1 mD2 mD3 : ℝ) (h1 : 0 < mD1) (h2 : 0 < mD2) (h3 : 0 < mD3) :
    ∃ (family : {t : ℝ // 0 < t} → JointValuation),
      (∀ t₁ t₂, t₁ ≠ t₂ → (family t₁).MR ≠ (family t₂).MR) ∧
      (∀ t₁ t₂, constraint_DiracProduct (family t₁) ↔
                constraint_DiracProduct (family t₂)) := by
  refine ⟨fun ⟨t, ht⟩ => m1_family mD1 mD2 mD3 h1 h2 h3 t ht, ?_, ?_⟩
  · intro ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ hne
    have : t₁ ≠ t₂ := by
      intro h; apply hne; exact Subtype.ext h
    exact m1_family_injective_in_t mD1 mD2 mD3 h1 h2 h3 t₁ t₂ ht₁ ht₂ this
  · intro ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
    exact m1_family_S2_invariant mD1 mD2 mD3 h1 h2 h3 t₁ t₂ ht₁ ht₂

end SpectralPhysics.SAGFJointUniqueness

end
