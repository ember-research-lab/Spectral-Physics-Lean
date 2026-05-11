/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SelfModelDeficit.Yukawas
import SpectralPhysics.SelfModelDeficit.SeeSawCancel
import SpectralPhysics.MajoranaBlock.SpectralMultiplicity
import SpectralPhysics.MajoranaBlock.HypothesisB
import SpectralPhysics.MajoranaBlock.Discriminator
import SpectralPhysics.IndexJSelfConj.JSelfConjBlock
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# `ζ_F(s; ν_R)`: the J-restricted zeta function on the (1,1)_0 sub-block

## Hypothesis under test (third attack vector)

> The ζ-function regularization of `D_F` *restricted to the
> J-self-conjugate (1,1)_0 = ν_R sub-block* yields a structural
> integer at `s = 0` (namely `8` in the τ^8 conjecture, or some
> other forcing constant) that closes the `y_R` bottleneck.
>
> If `ζ_F(0; ν_R)` is a structural integer `N`, the closure
> `−ζ̃'_vis(0) = 288` may force `−log y_R = (N · cleaner)`.

This file builds the restricted ζ-function

  `ζ_F(s; ν_R) = Σ_{mode m ∈ (1,1)_0 sub-block} (mult m) · y_m^{-2s}`,

abstractly, with the multiplicity provided by the discriminator from
`compute/majorana-block-residue` (Hypothesis B → multiplicity 6, the
standard-NCG choice; Hypothesis A → multiplicity 1, the non-standard
J-quotient).  The Mellin transform machinery is summarized in
`ResidueAtZero.lean`; the closure refinement test in
`ClosureRefinement.lean`; the verdict in `Verdict.lean`.

## Structural setup

In the finite spectral triple `(A_F, H_F, D_F)`, the eigenvalues of
`|D_F|` are exactly the singular values of the fermion mass matrix
`M`, scaled by the electroweak vev (`y_f = √2 m_f / v`).  The full
visible-sector ζ-function is

  `ζ̃_F(s) = Σ_f mult_f · y_f^{-2s}`

(see `Yukawas.lean`).  Restricted to the J-self-conjugate (1,1)_0
sub-block (the right-handed neutrino sector), only the `ν_R` mode
contributes:

  `ζ̃_F(s; ν_R) = mult_νR · y_R^{-2s}`,

where `mult_νR ∈ {1, 6}` per Hypothesis A vs B.

## What this file establishes

* The abstract definition of `zetaF_nuR (mult : ℕ) (y_R : ℝ) (s : ℝ)`.
* Tier-1 evaluation at `s = 0`: `zetaF_nuR mult y_R 0 = mult`.
* A degeneracy lemma: at `s = 0`, the J-restricted ζ-function carries
  only the multiplicity, *NOT* `y_R`.  In particular, the equation
  `ζ_F(0; ν_R) = 8` reduces to `mult = 8`, and standard NCG gives
  `mult = 6 ≠ 8`.

## Tier classification

* **Tier 1 (proved)**: `zetaF_nuR _ _ 0 = mult` for any positive
  `y_R`; the standard-NCG multiplicity 6 ≠ 8.
* **Tier 2 (named axiom)**: the fact that `Tr |D_F|^{-s}` (regularized)
  for a finite spectral triple equals the formal sum over eigenvalues;
  this is structural for finite-dim H_F.

## References

* Connes, A. & Marcolli, M. (2008), *Noncommutative Geometry, Quantum
  Fields and Motives*, AMS Coll. Pub. **55**, §1.7.4.
* Berline, N., Getzler, E. & Vergne, M. (1992), *Heat Kernels and
  Dirac Operators*, Springer Grundlehren **298**, Theorem 9.35.
* Ben-Shalom, "Spectral Physics", v0.9, Proposition `prop:zeta-explicit`
  (line 8402, eq. 8405).
-/

namespace SpectralPhysics.ZetaFNuR

open Real
open SpectralPhysics.SelfModelDeficit
open SpectralPhysics.MajoranaBlock

/-! ## The J-restricted ζ-function -/

/-- The J-restricted ζ-function `ζ_F(s; ν_R)` over the (1,1)_0
    sub-block of `D_F`.

    Abstract form: a single eigenvalue `y_R` with multiplicity `mult`
    contributes `mult · y_R^{-2s}`.

    For a *finite* spectral triple, `ζ_F` is well-defined for all
    `s ∈ ℂ` (no continuation needed) — the sum is finite.

    `noncomputable` because of `Real.rpow`. -/
noncomputable def zetaF_nuR (mult : ℕ) (y_R s : ℝ) : ℝ :=
  (mult : ℝ) * Real.rpow y_R (-2 * s)

/-- For positive `y_R`, the J-restricted ζ-function is strictly
    positive at any real `s`.  -/
theorem zetaF_nuR_pos {mult : ℕ} {y_R : ℝ} (hmult : 0 < mult)
    (hy : 0 < y_R) (s : ℝ) :
    0 < zetaF_nuR mult y_R s := by
  unfold zetaF_nuR
  have : (0 : ℝ) < (mult : ℝ) := by exact_mod_cast hmult
  exact mul_pos this (Real.rpow_pos_of_pos hy _)

/-! ## Evaluation at `s = 0`: the multiplicity is the residue -/

/-- **Tier 1 — the central degeneracy of the J-restricted ζ at `s = 0`.**

    For any `y_R > 0`,

      `ζ_F(0; ν_R) = mult`.

    *Proof*: `y_R^{-2·0} = y_R^0 = 1`, so the sum collapses to
    `mult · 1 = mult`.

    **Implication**: the value at `s = 0` is *independent of `y_R`*.
    Any structural integer the J-restricted ζ-function can produce at
    `s = 0` is the *multiplicity itself*.  Hence the closure
    `ζ_F(0; ν_R) = 8` reduces to `mult = 8`, which is *false* under
    Hypothesis B (standard NCG, `mult = 6`) and false under
    Hypothesis A (non-standard J-quotient, `mult = 1`). -/
theorem zetaF_nuR_at_zero {mult : ℕ} {y_R : ℝ} (_hy : 0 < y_R) :
    zetaF_nuR mult y_R 0 = (mult : ℝ) := by
  unfold zetaF_nuR
  have h : Real.rpow y_R (-2 * 0) = 1 := by
    have h0 : (-2 * 0 : ℝ) = 0 := by ring
    rw [h0]
    exact Real.rpow_zero _
  rw [h]; ring

/-- The restricted ζ-function at `s = 0` does NOT depend on `y_R`. -/
theorem zetaF_nuR_at_zero_indep_of_yR {mult : ℕ} {y₁ y₂ : ℝ}
    (h₁ : 0 < y₁) (h₂ : 0 < y₂) :
    zetaF_nuR mult y₁ 0 = zetaF_nuR mult y₂ 0 := by
  rw [zetaF_nuR_at_zero h₁, zetaF_nuR_at_zero h₂]

/-! ## Concrete instantiation under Hypothesis A vs B -/

/-- **Hypothesis A** (non-standard J-quotient, single-mode reading):
    `mult = 1`. -/
def multA : ℕ := 1

/-- **Hypothesis B** (standard NCG, three-generation Dirac doubling):
    `mult = 6`.  -/
def multB : ℕ := 6

/-- The discriminator integer `mult_B = 6` agrees with the framework's
    standard-NCG count, by `compute/majorana-block-residue`. -/
theorem multB_eq_NCG :
    multB = SpectralPhysics.MajoranaBlock.three_gen_dirac_multiplicity := rfl

/-- **Tier 1.**  Under Hypothesis A, the J-restricted residue at `s = 0`
    is exactly `1`. -/
theorem zetaF_nuR_at_zero_hypA {y_R : ℝ} (hy : 0 < y_R) :
    zetaF_nuR multA y_R 0 = 1 := by
  rw [zetaF_nuR_at_zero hy]
  unfold multA; simp

/-- **Tier 1.**  Under Hypothesis B, the J-restricted residue at `s = 0`
    is exactly `6`. -/
theorem zetaF_nuR_at_zero_hypB {y_R : ℝ} (hy : 0 < y_R) :
    zetaF_nuR multB y_R 0 = 6 := by
  rw [zetaF_nuR_at_zero hy]
  unfold multB; simp

/-! ## Comparison to the τ^8 conjecture and other structural integers

The hypothesis under test asked whether `ζ_F(0; ν_R) = 8` (the τ^8
exponent in `y_R = τ^8`).  By the degeneracy lemma above, this holds
iff `mult = 8` — but the standard-NCG multiplicity is 6, and the
non-standard reading is 1.  No NCG construction yields `mult = 8`. -/

/-- The structural integer `8` (target of the τ^8 conjecture). -/
def target_eight : ℕ := 8

/-- Other candidate structural integers in the framework: `1, 6, 8,
    16, 24, 32`. -/
def candidate_integers : List ℕ := [1, 6, 8, 16, 24, 32]

/-- **Tier 1.**  Standard NCG multiplicity (Hypothesis B) does NOT
    equal the τ^8 target. -/
theorem multB_ne_eight : multB ≠ target_eight := by
  unfold multB target_eight; decide

/-- **Tier 1.**  Non-standard J-quotient multiplicity (Hypothesis A)
    does NOT equal the τ^8 target. -/
theorem multA_ne_eight : multA ≠ target_eight := by
  unfold multA target_eight; decide

/-- **Tier 1 — direct falsification of the `ζ_F(0; ν_R) = 8`
    hypothesis.**  Under either NCG reading (Hypothesis A or B),

      `ζ_F(0; ν_R) ≠ 8`. -/
theorem zetaF_nuR_at_zero_ne_eight {y_R : ℝ} (hy : 0 < y_R) :
    zetaF_nuR multA y_R 0 ≠ (8 : ℝ) ∧
    zetaF_nuR multB y_R 0 ≠ (8 : ℝ) := by
  refine ⟨?_, ?_⟩
  · rw [zetaF_nuR_at_zero_hypA hy]; norm_num
  · rw [zetaF_nuR_at_zero_hypB hy]; norm_num

end SpectralPhysics.ZetaFNuR
