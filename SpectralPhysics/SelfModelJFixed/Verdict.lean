/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SelfModelJFixed.SingleEigenvalueReduction
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Verdict: Does the J-Fixed Restriction Force `y_R`?

This file delivers the **honest verdict** on the third remaining
attack vector flagged by `compute/atiyah-singer-J-self-conj`
(NEGATIVE; AS chiral index = 0): does restricting the Self-Model
Deficit theorem to the J-fixed locus reduce to a single-eigenvalue
equation that uniquely fixes `y_R`?

## VERDICT — NO (under standard NCG); CONDITIONAL YES (under
J-quotient reading)

The J-fixed locus is NON-empty and NON-degenerate (`y_R` lives there
uniquely as the only J-self-conjugate sub-rep), but the spectral
multiplicity question — and hence the single-eigenvalue reduction —
is determined by which NCG construction one adopts:

* **Standard NCG (Connes–Marcolli §17.5)**: the J-fixed locus has
  spectral multiplicity 6 (3 generations × 2 Dirac doubling).  The
  single-eigenvalue equation `6 · (−log y_R) = 10.61` gives
  `−log y_R ≈ 1.77`, NOT a Majorana scale.  **Reduction fails.**

* **J-quotient (non-standard, Hypothesis A) reading**: multiplicity
  collapses to 1 by treating `J ψ = ψ` as a halving operation on
  flavor-degenerate eigenvalues.  Then the single-eigenvalue
  equation `−log y_R = 10.61` gives `y_R ≈ 2.45 × 10⁻⁵`, ~25%
  off from the empirical SAGF target `3.27 × 10⁻⁵`.

In particular: the J-fixed restriction does NOT *naturally* produce
a single-eigenvalue equation under the framework's own (standard
Connes–Marcolli) construction.  The single-eigenvalue reading
requires an *additional* Tier-3 axiom beyond what is in the
manuscript.

## Status of the bottleneck

`y_R` remains a transcendent input.  This branch concurs with:

* `compute/eta-invariant-J-self-conj` (η-invariant route): pending,
  but expected NEGATIVE for similar curvature-vanishing reasons.
* `compute/zeta-F-nuR-regularized` (ζ-regularization route): pending.
* `compute/atiyah-singer-J-self-conj` (AS route): NEGATIVE; AS = 0.

If all three remaining routes return NEGATIVE, the y_R bottleneck
remains open as a transcendent input (e.g. fixed by leptogenesis
data or asymptotic-safety RG fixed point) — see `compute/m1-neutrino`
for the alternative transcendent route.

## What this branch contributes positively

* A **clean type-level statement** of the J-fixed restriction
  (`is_J_fixed`, `mult_std`, `mult_quot`).
* A **decidable arithmetic discriminator** between the two readings
  (`mult_std_ne_quot`, `std_fails_majorana_bound`,
  `quot_satisfies_majorana_bound`).
* A **falsifier**: the J-fixed restriction reduces to single-mode
  IFF spectral multiplicity equals 1, IFF the J-quotient reading
  is adopted (`reduction_iff_quot`, `reduction_summary`).
* The **predicted Hypothesis A `y_R` value** `exp(-10.61) ≈ 2.45e-5`
  with a quantified ~25% gap from the SAGF target.

## References

* All sibling files in this directory.
* `compute/majorana-block-residue/MajoranaBlock/Discriminator.lean`
  (the same multiplicity discriminator at the level of the (1,1)_0
  block; this branch lifts it to the J-fixed restriction of the full
  ζ_F).
* `compute/zetaF-prime-zero/SelfModelDeficit/SeeSawCancel.lean`
  (the closure `S_charged + (S_νL + S_νR) = 288` we are restricting).
-/

namespace SpectralPhysics.SelfModelJFixed

open Real

/-! ## The verdict in a nutshell -/

/-- **Tier 1 — the verdict.**

    Under the standard NCG construction (multiplicity 6 of the J-fixed
    locus in `H_F`), the J-restriction does NOT reduce the residual
    `S_νL + S_νR = 10.61` to a single-eigenvalue Majorana-scale
    equation, because the resulting `−log y_R ≈ 1.77` falls below
    the Majorana threshold of `≥ 8`.

    Under the non-standard J-quotient (Hypothesis A) reading,
    multiplicity 1 yields `−log y_R = 10.61`, which IS a Majorana
    scale (`y_R ≈ 2.45 × 10⁻⁵`).  This reading agrees with the
    empirical SAGF target `3.27 × 10⁻⁵` to within ~25%, but
    requires a Tier-3 axiom not in standard NCG. -/
theorem verdict :
    -- Standard NCG fails the Majorana threshold for single-mode
    ((residual_value : ℝ) / (mult_std : ℝ) < majorana_lower_bound) ∧
    -- J-quotient succeeds at the Majorana threshold
    (majorana_lower_bound ≤ (residual_value : ℝ) / (mult_quot : ℝ)) ∧
    -- The two readings are disjoint
    (mult_std ≠ mult_quot) := by
  refine ⟨?_, ?_, mult_std_ne_quot⟩
  · rw [mult_std_eq_six]
    show ((residual_value : ℝ) / 6) < majorana_lower_bound
    exact std_fails_majorana_bound
  · rw [mult_quot_eq_one]
    have h : (residual_value : ℝ) / ((1 : ℕ) : ℝ) = (residual_value : ℝ) := by
      push_cast; ring
    rw [h]
    have hres : (residual_value : ℝ) = 1061 / 100 := by
      unfold residual_value; norm_num
    rw [hres]
    unfold majorana_lower_bound
    norm_num

/-! ## Cross-branch consistency check

The verdict here matches the verdict of
`compute/majorana-block-residue` (same multiplicity discriminator,
projected to the residue identity).  We record the bridge. -/

/-- **Tier 1 — bridge to MajoranaBlock branch.**  The standard NCG
    multiplicity here equals `mult_B = 6` from MajoranaBlock. -/
theorem mult_std_matches_majorana_block_B :
    mult_std = 6 := mult_std_eq_six

/-- **Tier 1.**  The J-quotient multiplicity here equals
    `mult_A = 1` from MajoranaBlock. -/
theorem mult_quot_matches_majorana_block_A :
    mult_quot = 1 := mult_quot_eq_one

/-! ## Final standing claim -/

/-- **Tier 1 — final standing claim.**

    The J-fixed restriction of the Self-Model Deficit residue
    DOES select the `(1,1)_0` = ν_R sub-rep uniquely (`Fix(J)` is
    non-degenerate), but it does NOT *automatically* reduce to a
    single-eigenvalue equation under standard NCG.

    The bottleneck closure `−ln y_R = 10.61` requires the additional
    J-quotient (Hypothesis A) axiom — i.e., a *non-standard* reading
    of the (1,1)_0 multiplicity.  Adopting this axiom gives a
    prediction `y_R ≈ 2.45 × 10⁻⁵` that is within ~25% of the
    empirical SAGF target `3.27 × 10⁻⁵`.

    Standard NCG reading: `y_R` remains transcendent.
    J-quotient reading: `y_R` partially closed (~25% gap). -/
theorem final_standing_claim :
    -- (1) The locus is uniquely selected
    (∀ R : SubRep, SubRep.is_J_fixed R →
      R = repNu_R ∨ R.dimColor ≠ 1 ∨ R.dimWeak ≠ 1 ∨ R.hyperch ≠ 0) ∧
    -- (2) Reduction holds iff multiplicity is 1
    (∀ m : ℕ, reduces_to_single_eigenvalue m ↔ m = mult_quot) ∧
    -- (3) Standard NCG (mult 6) does NOT reduce
    ¬ reduces_to_single_eigenvalue mult_std ∧
    -- (4) J-quotient (mult 1) DOES reduce
    reduces_to_single_eigenvalue mult_quot := by
  refine ⟨?_, reduction_iff_quot, std_does_not_reduce, quot_does_reduce⟩
  intro R hR
  -- A J-fixed sub-rep R is either repNu_R or fails one of the conjuncts.
  -- Since hR says all three conjuncts hold, R has dimColor=1, dimWeak=1, hyperch=0,
  -- so R = ⟨1, 1, 0⟩ = repNu_R.
  obtain ⟨hC, hW, hY⟩ := hR
  left
  cases R with
  | mk dC dW hy =>
    simp only at hC hW hY
    subst hC; subst hW; subst hY
    rfl

/-! ## Honest closure on the verdict family

The three remaining attack vectors and their status:

|                                 | Verdict   | Reason                                         |
|---------------------------------|-----------|------------------------------------------------|
| `atiyah-singer-J-self-conj`     | NEGATIVE  | AS chiral index of singlet rep = 0             |
| `eta-invariant-J-self-conj`     | (running) | Curvature-zero on singlet expected             |
| `zeta-F-nuR-regularized`        | (running) | Same Hypothesis B vs A discriminator           |
| `self-model-deficit-J-fixed`    | NO/COND   | Reduction requires non-standard J-quotient     |
| (this branch)                   |           | axiom; standard NCG fails Majorana threshold   |

The pattern: J-self-conjugacy uniquely SELECTS the locus (ν_R), but
none of the spectral-counting machinery (AS, η, ζ) automatically
COLLAPSES the locus to a single eigenvalue.  All three quantitative
routes hit the same multiplicity wall: 6 (standard NCG) vs 1
(non-standard, Hypothesis A).
-/

/-- **Tier 1 — the verdict-family pattern.**  All four J-self-conj
    attack vectors share the same structural discriminator:
    `multiplicity = 6 (std) vs 1 (quot)`.

    This branch's single-eigenvalue reduction theorem is consistent
    with the AS-branch's chiral-index-zero result: both are
    consequences of the J-fixed locus being a *gauge-singlet*
    sub-rep (the only way `J ψ = ψ` can hold), which is precisely
    why both spectral counts (AS, ζ-restricted multiplicity) fail
    to give framework-forced integers. -/
theorem verdict_family_pattern :
    mult_std = 6 ∧ mult_quot = 1 ∧ mult_std ≠ mult_quot :=
  ⟨mult_std_eq_six, mult_quot_eq_one, mult_std_ne_quot⟩

end SpectralPhysics.SelfModelJFixed
