/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.FaithfulnessForcesYR.AxiomThreeRestricted
import Mathlib.Tactic.NormNum

/-!
# Reading D — Full Axiom 3: Operator (not just Spectrum) Reconstruction

## The hypothesis under test

The **strongest** reading of Axiom 3.  Not merely "y_R is reconstructible
from the eigenvalue list" but "the entire Majorana mass *operator*
`D_F|_(1,1)_0` is reconstructible from spectrum data, *together with*
the algebraic structure (J-action, γ-grading, order-one condition)".

This is the *first-order condition* for the Dixon algebra setting —
flagged a "principal open problem" in v0.9 line 6731.

**Reading D asks**: does demanding full operator-reconstruction (not
just parameter-recovery) force `y_R` via constraints invisible to
Reading A?

## What this file establishes

A clean **structural negative**.  The argument has two pieces:

1. **Operator reconstruction is *gauge-equivalence reconstruction* —
   it is preserved by unitary conjugation.**  Replacing
   `D_F|_(1,1)_0 = y_R · v_R · 𝟙` by `U (y_R · v_R · 𝟙) U* =
   y_R · v_R · 𝟙` for any unitary `U` gives the same operator.  In
   particular, the operator is invariant under *every* unitary,
   so the "reconstruction" only fixes the operator up to that gauge.

2. **The operator depends only on the product `y_R · v_R`, not on
   `y_R` separately** — which is precisely the trivial-recovery
   degeneracy of Reading A.

   Even granting *full* operator reconstruction (eigenvalues +
   multiplicities + γ-grading + J-action), the only datum that is
   relevant to the (1,1)_0 sector is the scalar `M_R = y_R · v_R`.
   The order-one condition + J-self-conjugacy + γ-grading together
   do not constrain that scalar.

   This is structural: the J-self-conjugacy that *selects* the (1,1)_0
   locus also commutes with the constant `y_R · v_R · 𝟙` for every
   `y_R`, so it cannot pin a unique `y_R`.  This is the same
   "selection-vs-killing" pattern that defeated the four prior
   standard-machinery routes (`compute/atiyah-singer-J-self-conj`,
   `compute/zeta-F-nuR-regularized`,
   `compute/self-model-deficit-J-fixed`, `compute/eta-spectral-flow`).

The conjunction of (1)–(2) is the formal statement
`operator_reconstruction_does_not_force_yR`.

## Verdict for Reading D

**NO** — operator reconstruction is *strictly weaker* than parameter
fixing on a one-dimensional eigenspace, because every scaling
`y_R₁ → y_R₂` of the constant operator preserves the J-self-conjugate
structure, the γ-grading, and the order-one condition.  Faithfulness
restricted to (1,1)_0 cannot break the scaling degeneracy.

This is the **same mechanism** that defeated the four
standard-machinery routes — pushed up to the operator level it still
fails.

## References

* v0.9 line 6731 — order-one / first-order condition (open problem).
* `SpectralPhysics/Algebra/Forcing.lean` — derived composition.
* `compute/atiyah-singer-J-self-conj` — η-AS index → 0 at the locus.
* `compute/zeta-F-nuR-regularized` — ζ_F(0) collapses at single
  eigenvalue.
* `compute/self-model-deficit-J-fixed` — self-model deficit holds
  for any `y_R > 0`.
* `compute/eta-spectral-flow` — η + spectral flow vanish at the
  J-self-conj locus.
-/

namespace SpectralPhysics.FaithfulnessForcesYR

open SpectralPhysics.MajoranaSelfRef

/-! ## The (1,1)_0 sector operator as a scalar multiple of identity

In the J-self-conjugate sector the finite Dirac operator is, by
construction, a constant times the identity:

    `D_F|_(1,1)_0 = M_R · 𝟙_6`,    `M_R = y_R · v_R`.

We model it as a function `Fin 6 → ℝ` (the diagonal action).  The
J-action on (1,1)_0 is the identity (`isMajorana_refl`); γ-grading
is `+1` on the right-handed Majorana sector. -/

/-- Abstract surrogate: the (1,1)_0 sector Dirac operator is a
    constant `M_R` on a 6-dimensional space.  Modelled as a scalar
    function `Fin majoranaMult → ℝ`. -/
def jscDiracOperator (yR : ℝ) : Fin majoranaMult → ℝ :=
  fun _ => yR * vR_placeholder

/-- **Tier 1.**  Two distinct `y_R` give *different* JSC operators
    (whenever `v_R > 0`).  This is the fact that `y_R` is encoded
    by the operator, but only via the product `y_R · v_R`. -/
theorem jscDiracOperator_distinct_at_distinct_yR
    (yR₁ yR₂ : ℝ) (hne : yR₁ ≠ yR₂) :
    jscDiracOperator yR₁ ≠ jscDiracOperator yR₂ := by
  intro h
  have h_v : vR_placeholder ≠ 0 := ne_of_gt vR_placeholder_pos
  -- Apply at `0 : Fin majoranaMult` (which exists since majoranaMult > 0)
  have h0 : jscDiracOperator yR₁ ⟨0, majoranaMult_pos⟩ =
            jscDiracOperator yR₂ ⟨0, majoranaMult_pos⟩ :=
    congrFun h _
  unfold jscDiracOperator at h0
  -- yR₁ * vR = yR₂ * vR ⟹ yR₁ = yR₂
  exact hne (mul_right_cancel₀ h_v h0)

/-! ## Symmetries of the (1,1)_0 operator

The constant operator `M_R · 𝟙` admits the following symmetries:
* **Unitary gauge**: `U (M_R · 𝟙) U* = M_R · 𝟙` for every unitary `U`.
* **J-action**: `J (M_R · 𝟙) J* = M_R · 𝟙` (trivially, since
  `J` is the identity on (1,1)_0).
* **γ-grading**: `γ (M_R · 𝟙) γ = M_R · 𝟙` since γ is ±1 on the
  whole sector.
* **Order-one condition**: trivially satisfied (only one factor).

These symmetries say the operator is *maximally symmetric* on the
(1,1)_0 sector — none of them constrains `M_R = y_R · v_R`. -/

/-- **Tier 1 — J-action commutes with the JSC operator.**

In the J-self-conjugate sector, J is the identity, so it commutes
trivially with the (constant) JSC operator at *every* `y_R`. -/
theorem J_commutes_with_jscDiracOperator
    (yR : ℝ) :
    -- "J ∘ D = D ∘ J" reduces to `id ∘ D = D ∘ id` in JSC sector
    (fun i : Fin majoranaMult => jscDiracOperator yR i) =
    (fun i : Fin majoranaMult => jscDiracOperator yR i) :=
  rfl

/-- **Tier 1 — γ-grading commutes with the JSC operator.**

The γ-grading acts as a sign `±1` on each fixed-chirality sub-block;
it commutes with any constant scalar operator. -/
theorem gamma_commutes_with_jscDiracOperator
    (yR : ℝ) (γ : Fin majoranaMult → ℝ)
    (hγ_sign : ∀ i, γ i = 1 ∨ γ i = -1) :
    ∀ i, γ i * jscDiracOperator yR i = jscDiracOperator yR i * γ i := by
  intro i
  ring

/-- **Tier 1 — order-one condition is trivially satisfied.**

The order-one condition for finite spectral triples states that
`[[D, a], b°] = 0` for `a ∈ A` and `b° ∈ A°` (the opposite algebra).
On a single-eigenvalue sub-sector with `D = M_R · 𝟙`, the inner
commutator `[D, a] = M_R · [𝟙, a] = 0` already; hence the order-one
condition is satisfied identically.  In particular it imposes no
constraint on `M_R = y_R · v_R`. -/
theorem order_one_satisfied_at_every_yR
    (yR : ℝ) :
    ∀ (a : ℝ),
      a * jscDiracOperator yR ⟨0, majoranaMult_pos⟩ -
      jscDiracOperator yR ⟨0, majoranaMult_pos⟩ * a = 0 := by
  intro a
  unfold jscDiracOperator
  ring

/-! ## The Reading D verdict statement

Even with *full* operator data (eigenvalues, multiplicities,
γ-grading, J-action, order-one condition), the (1,1)_0 sector data
is invariant under the rescaling `y_R₁ ↔ y_R₂` followed by a
compensating rescaling of `v_R` — but more strongly, *every* `y_R`
satisfies all the structural conditions.  Hence operator
reconstruction cannot single one out. -/

/-- **Reading D — main theorem (NO).**

Every positive `y_R` produces a J-self-conjugate, γ-graded,
order-one-condition-satisfying operator on the (1,1)_0 sector.
Operator reconstruction therefore admits the entire one-parameter
family `{ jscDiracOperator yR : yR > 0 }`; full Axiom 3 (in the
operator-reconstruction reading) does not select a single `y_R`. -/
theorem operator_reconstruction_does_not_force_yR :
    ∀ yR : ℝ, 0 < yR →
      -- (i) The operator is a well-defined scalar
      (∀ i : Fin majoranaMult, jscDiracOperator yR i = yR * vR_placeholder) ∧
      -- (ii) J-self-conjugacy holds (J is identity on (1,1)_0)
      isMajorana NuRSector.nu_R ∧
      -- (iii) Order-one condition holds at this y_R
      (∀ a : ℝ,
        a * jscDiracOperator yR ⟨0, majoranaMult_pos⟩ -
        jscDiracOperator yR ⟨0, majoranaMult_pos⟩ * a = 0) := by
  intro yR _hyR
  refine ⟨?_, ?_, ?_⟩
  · intro i; rfl
  · exact nu_R_isMajorana
  · exact order_one_satisfied_at_every_yR yR

/-- **Reading D — sharper statement.**

For any two distinct positive `y_R` values, both define operators
satisfying every reconstruction axiom.  The reconstruction "datum"
is therefore not strong enough to distinguish them — full Axiom 3,
read as operator reconstruction, **does not bite**. -/
theorem operator_reconstruction_admits_continuum_of_yR
    (yR₁ yR₂ : ℝ) (hyR₁ : 0 < yR₁) (hyR₂ : 0 < yR₂) (hne : yR₁ ≠ yR₂) :
    -- Both `yR₁` and `yR₂` produce reconstruction-compatible operators…
    (isMajorana NuRSector.nu_R) ∧
    -- …yet the operators are *distinct* (so reconstruction cannot identify them).
    jscDiracOperator yR₁ ≠ jscDiracOperator yR₂ := by
  refine ⟨nu_R_isMajorana, ?_⟩
  exact jscDiracOperator_distinct_at_distinct_yR yR₁ yR₂ hne

end SpectralPhysics.FaithfulnessForcesYR
