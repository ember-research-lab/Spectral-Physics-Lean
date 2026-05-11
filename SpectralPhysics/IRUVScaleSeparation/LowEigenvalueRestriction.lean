/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.IRUVScaleSeparation.CutoffFamily

/-!
# Low-Eigenvalue Restriction and IR Stability

For a cutoff family `R : CutoffFamily` and a *low-energy scale*
`μ > 0` with `μ ≪ Λ`, the **low-eigenvalue restriction** of
`D_F(Λ)` is the sub-sequence of eigenvalues `n ↦ λ_n(Λ)` of
`D_F(Λ)` satisfying `|λ_n(Λ)| ≤ μ`.

The IR/UV-separation hypothesis of v0.9 (`prop:spectral-convergence`,
line 1437) is:

  ∀ Λ, Λ' with Λ_IR ≤ Λ ≤ Λ',
    restrictTo μ (D_F(Λ))  ≃  restrictTo μ (D_F(Λ'))

where `≃` is isospectrality (and at the operator level, unitary
equivalence) of the low-mode sub-sequences.

This file defines:

* `restrictTo R μ Λ` — the predicate `eigenvalue ≤ μ` at cutoff Λ,
  as a function `ℕ → Prop`. The "restricted spectrum" is the
  sub-sequence `{n : ℕ | restrictTo R μ Λ n}`.
* `LowEnergyAgree R μ Λ Λ'` — predicate stating the low-energy
  restrictions at `Λ` and `Λ'` agree as multi-sets of eigenvalues.
  This is the IR/UV-separation content at the eigenvalue level.
* `IRStability R μ` — the v0.9 IR-stability predicate: for every
  pair `Λ_IR ≤ Λ ≤ Λ'`, `LowEnergyAgree R μ Λ Λ'`.

## Honest scope

* "Isospectrality" is captured at the eigenvalue level as pointwise
  equality `R.D_F Λ n = R.D_F Λ' n` whenever the eigenvalue is in
  the low-mode band `[0, μ]`. The unitary-equivalence layer is *not*
  formalised (we do not have `D_F(Λ)` as a Hilbert-space operator);
  the eigenvalue agreement is the substantive content downstream.
* "Restriction" is the eigenvalue-level predicate
  `R.D_F Λ n ≤ μ`. The full eigenfunction structure is out of scope.

## References

* Ben-Shalom (2026). *Spectral Physics* v0.9, line 1437.
* Kato (1995) §V.4 (Stability of finite systems of eigenvalues).
* Reed–Simon Vol. IV (1978), §XIII.5 (Schatten-norm convergence).
-/

namespace SpectralPhysics.IRUVScaleSeparation

/-! ## The low-eigenvalue restriction predicate -/

/-- A natural number `n` belongs to the **low-eigenvalue band**
    at cutoff `Λ` and scale `μ` iff the `n`-th eigenvalue of
    `D_F(Λ)` is in `[0, μ]`.

    Mnemonic: `restrictTo R μ Λ n` is true iff the `n`-th
    eigenvalue is "kept" by the low-pass restriction. -/
def restrictTo (R : CutoffFamily) (μ : ℝ) (Λ : ℝ) (n : ℕ) : Prop :=
  R.D_F Λ n ≤ μ

/-- The restriction at any non-negative `μ` keeps the zero-modes:
    eigenvalues equal to `0` are always in the band.

    This is a sanity lemma: the kernel of `D_F` is universal. -/
theorem restrictTo_zero
    (R : CutoffFamily) (μ : ℝ) (Λ : ℝ) (n : ℕ)
    (h : R.D_F Λ n = 0) (hμ : 0 ≤ μ) :
    restrictTo R μ Λ n := by
  unfold restrictTo
  rw [h]
  exact hμ

/-! ## Low-energy agreement at two cutoffs -/

/-- **Low-energy agreement.**  At scales `Λ` and `Λ'` (both above
    the IR scale), the two restricted spectra agree as functions
    `ℕ → ℝ` *on the low-mode band*: for every `n` with the `n`-th
    eigenvalue at `Λ` in `[0, μ]`, the eigenvalue at `Λ'` agrees,
    and *vice versa*.

    This is the substantive content of v0.9's "low-eigenvalue
    spectrum is consistent across cutoffs". -/
def LowEnergyAgree (R : CutoffFamily) (μ : ℝ) (Λ Λ' : ℝ) : Prop :=
  ∀ (n : ℕ),
    (restrictTo R μ Λ  n → R.D_F Λ n = R.D_F Λ' n)
  ∧ (restrictTo R μ Λ' n → R.D_F Λ n = R.D_F Λ' n)

/-- Low-energy agreement is **symmetric** in `Λ ↔ Λ'`. -/
theorem LowEnergyAgree.symm
    {R : CutoffFamily} {μ Λ Λ' : ℝ}
    (h : LowEnergyAgree R μ Λ Λ') :
    LowEnergyAgree R μ Λ' Λ := by
  intro n
  refine ⟨?_, ?_⟩
  · intro h_low
    exact ((h n).2 h_low).symm
  · intro h_low
    exact ((h n).1 h_low).symm

/-- Low-energy agreement is **reflexive**: every family agrees with
    itself. -/
theorem LowEnergyAgree.refl
    (R : CutoffFamily) (μ : ℝ) (Λ : ℝ) :
    LowEnergyAgree R μ Λ Λ := by
  intro n
  exact ⟨fun _ => rfl, fun _ => rfl⟩

/-! ## IR stability — the v0.9 universality content -/

/-- **IR stability at scale `μ`.**  For every pair of UV cutoffs
    `Λ ≤ Λ'` above the IR scale, the low-eigenvalue restrictions
    agree.

    This is the v0.9 IR/UV-separation content at scale `μ`:
    low-energy observables (eigenvalues below `μ`) depend only on
    the IR scale, not on the UV regulator. -/
def IRStability (R : CutoffFamily) (μ : ℝ) : Prop :=
  ∀ (Λ Λ' : ℝ), R.Λ_IR ≤ Λ → Λ ≤ Λ' → LowEnergyAgree R μ Λ Λ'

/-- **Symmetric form of IR stability.**  Combining `IRStability`
    with `LowEnergyAgree.symm`, the low-mode restrictions agree
    for any pair of UV cutoffs above the IR scale (without the
    `Λ ≤ Λ'` orientation requirement). -/
theorem IRStability.symmetric
    {R : CutoffFamily} {μ : ℝ}
    (h : IRStability R μ)
    (Λ Λ' : ℝ) (hΛ : R.Λ_IR ≤ Λ) (hΛ' : R.Λ_IR ≤ Λ') :
    LowEnergyAgree R μ Λ Λ' := by
  by_cases h_ord : Λ ≤ Λ'
  · exact h Λ Λ' hΛ h_ord
  · have h_ord' : Λ' ≤ Λ := le_of_lt (lt_of_not_ge h_ord)
    exact (h Λ' Λ hΛ' h_ord').symm

end SpectralPhysics.IRUVScaleSeparation
