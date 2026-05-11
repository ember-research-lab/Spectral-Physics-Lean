/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.MajoranaBlock.SpectralMultiplicity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Hypothesis A — single-mode (1,1)_0 contribution via the
non-standard J-quotient construction

## Redemption notice

The prior version of this file shipped a "headline" theorem

```
theorem hypothesisA_multiplicity :
    SpectralPhysics.MajoranaBlock.single_mode_multiplicity = 1 := rfl
```

with `single_mode_multiplicity : ℕ := 1` — pure `1 = 1` by `rfl`.
Audit caught this as definitional content masquerading as a
structural result.

This file replaces the bare `1` with the **conditional theorem**
that Hypothesis A's multiplicity = 1 follows from a clearly tagged
*non-standard* J-quotient axiom, not from definitional triviality.

## Structural statement of Hypothesis A

Hypothesis A claims:

  > The J-self-conjugate (1,1)_0 sub-block of `H_F` contributes
  > **exactly one** mode to `Tr |D_F|^{-s}`, regardless of the
  > 3-generation flavor structure.

For this to hold within an NCG framework, the spectral triple
must use a **non-standard J-quotient construction** that
identifies particle and charge-conjugate at the Hilbert-space
level, AND collapses the 3 generations to a flavor-diagonal
scalar.  Neither operation is in Connes-Marcolli §17.5 or any
published NCG framework.

Hence the headline theorem of this file is the *conditional*

  `usesJQuotientAxiom T → JSC_multiplicity_under_quotient T = 1`,

which is honest: the conclusion follows ONLY if the non-standard
axiom is admitted.

## Tier classification

* **Tier 1**: the conditional structure of the theorem, the
  numerical bookkeeping for `−log y_R` (positivity at the SAGF
  target).
* **Tier 3 (non-standard)**: the axiom
  `j_quotient_axiom_collapses_multiplicity` in
  `SpectralMultiplicity.lean`.  Explicit non-standard tag.

## References

* Connes-Marcolli (2008) §17.5 — the *standard* construction
  (extended Dirac), which does NOT support Hypothesis A.
* Ben-Shalom, "Spectral Physics", v0.9, pre-geometric
  `baker_selects_yR/verdict.md` (defines Hypothesis A).
-/

namespace SpectralPhysics.MajoranaBlock.HypothesisA

open Real
open SpectralPhysics.MajoranaBlock

/-! ## Definition of Hypothesis A as a predicate on the spectral triple

Hypothesis A is the predicate that the (hypothetical) spectral
triple uses the non-standard J-quotient construction. -/

set_option linter.dupNamespace false in
/-- **Hypothesis A (as a predicate on the spectral triple).**

The triple uses the non-standard J-quotient construction, in which
`H_F` is quotiented by `J` rather than doubled.  This is the
structural commitment that licenses the multiplicity-1 reading. -/
def HypothesisA (T : FiniteSpectralTriple) : Prop :=
  T.usesJQuotientAxiom

/-- **Tier 1.**  Hypothesis A holding rules out the extended-Dirac
construction. -/
theorem HypothesisA_excludes_extendedDirac
    (T : FiniteSpectralTriple) (h : HypothesisA T) :
    ¬ T.usesExtendedDiracConstruction := by
  intro h_ext
  exact extendedDirac_and_JQuotient_disjoint T ⟨h_ext, h⟩

/-! ## The headline theorem (HONEST — depends on Tier-3 axiom) -/

/-- **HEADLINE — Hypothesis A.**

For any KO-dim 6 finite spectral triple `T` with J-signs
`(1, 1, -1)` that satisfies Hypothesis A (i.e. uses the
non-standard J-quotient construction), the J-self-conjugate
multiplicity under the quotient is exactly 1.

The proof unpacks the existential in the named (non-standard)
axiom `j_quotient_axiom_collapses_multiplicity`.  It is **not**
`1 = 1` by `rfl`: it consumes the Tier-3 axiom whose existence is
the operator-algebraic content. -/
theorem hypothesis_A_requires_J_quotient
    (T : FiniteSpectralTriple)
    (h_kodim : T.KOdim_eq_six)
    (h_J : T.J_sign_triple_KO6)
    (h_HypA : HypothesisA T) :
    JSC_multiplicity_under_quotient T h_kodim h_J h_HypA = 1 := by
  unfold JSC_multiplicity_under_quotient
  -- Unpacks the existential supplied by the Tier-3 non-standard
  -- axiom `j_quotient_axiom_collapses_multiplicity`.
  exact Classical.choose_spec
    (j_quotient_axiom_collapses_multiplicity T h_kodim h_J h_HypA)

/-- **Corollary.**  Under Hypothesis A, the multiplicity is
independent of the generation count.  This is the "flavor-collapse"
feature of the J-quotient convention. -/
theorem HypothesisA_flavor_collapsed
    (T₁ T₂ : FiniteSpectralTriple)
    (h_kodim₁ : T₁.KOdim_eq_six) (h_J₁ : T₁.J_sign_triple_KO6)
    (h_HypA₁ : HypothesisA T₁)
    (h_kodim₂ : T₂.KOdim_eq_six) (h_J₂ : T₂.J_sign_triple_KO6)
    (h_HypA₂ : HypothesisA T₂) :
    JSC_multiplicity_under_quotient T₁ h_kodim₁ h_J₁ h_HypA₁ =
      JSC_multiplicity_under_quotient T₂ h_kodim₂ h_J₂ h_HypA₂ := by
  rw [hypothesis_A_requires_J_quotient T₁ h_kodim₁ h_J₁ h_HypA₁,
      hypothesis_A_requires_J_quotient T₂ h_kodim₂ h_J₂ h_HypA₂]

/-! ## Numerical bookkeeping — `−log y_R` at the SAGF target

Once the multiplicity-1 claim is in place, the residue contribution
under Hypothesis A is `S_νR^A = 1 · (−log y_R) = −log y_R`.
We retain the Tier-1 positivity bookkeeping from the prior version,
since these are genuine arithmetic identities (not `rfl` on
integers). -/

/-- The right-handed neutrino Yukawa at the SAGF-bisected target,
`y_R = M_R/σ_0 ≈ 3.27·10⁻⁵`. -/
noncomputable def y_R_target : ℝ := 327 / 10000000

/-- **Tier 1.**  `y_R > 0`. -/
theorem y_R_target_pos : 0 < y_R_target := by
  unfold y_R_target; norm_num

/-- **Tier 1.**  `y_R < 1`. -/
theorem y_R_target_lt_one : y_R_target < 1 := by
  unfold y_R_target; norm_num

/-- The Hypothesis A single-mode residue contribution from the
(1,1)_0 sub-block, assuming multiplicity 1: `S_νR^A = −log y_R`. -/
noncomputable def contribution (y_R : ℝ) : ℝ := -Real.log y_R

/-- **Tier 1.**  For `0 < y_R < 1`, the contribution is positive. -/
theorem contribution_pos (y_R : ℝ) (h₁ : 0 < y_R) (h₂ : y_R < 1) :
    0 < contribution y_R := by
  unfold contribution
  have : Real.log y_R < 0 := Real.log_neg h₁ h₂
  linarith

/-- **Tier 1.**  Hypothesis A's contribution at the SAGF target
is positive. -/
theorem contribution_at_target_pos : 0 < contribution y_R_target :=
  contribution_pos y_R_target y_R_target_pos y_R_target_lt_one

/-! ## Honest assessment — what this file does NOT prove

* It does NOT prove Hypothesis A holds in the physical SM.  In fact
  the SM canonical triple `standardModelTriple` has
  `extendedDirac = true` (the standard convention), which by
  `extendedDirac_and_JQuotient_disjoint` rules out `HypothesisA`.
* It does NOT derive the multiplicity-1 collapse from first
  principles.  The Tier-3 axiom
  `j_quotient_axiom_collapses_multiplicity` is precisely the
  non-standard input that *would* license Hypothesis A — and we
  flag it as not present in any published NCG framework.

The honest content of this file is: **IF** one is willing to admit
the non-standard J-quotient axiom, **THEN** the multiplicity-1
reading of the (1,1)_0 sub-block follows.  The published SM finite
spectral triple does not admit this axiom. -/

/-- **Tier 1 — sanity check.**  The canonical SM triple does NOT
satisfy Hypothesis A (since it uses the standard extended-Dirac
construction).  This is the negative anchor: Hypothesis A is
defensible only under non-standard NCG. -/
theorem standardModelTriple_violates_HypothesisA :
    ¬ HypothesisA standardModelTriple :=
  standardModelTriple_not_JQuotient

end SpectralPhysics.MajoranaBlock.HypothesisA
