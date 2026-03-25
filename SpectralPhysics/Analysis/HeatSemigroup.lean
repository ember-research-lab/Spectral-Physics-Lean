/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Axioms.Laplacian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Heat Semigroup via Spectral Decomposition

The heat semigroup `e^{-tL}` constructed from the spectral decomposition of `L`.
In finite dimensions, every self-adjoint operator has an orthonormal eigenbasis.
We axiomatize this as `SpectralDecomp` and define `heatInner` from it.

## Main definitions

* `SpectralDecomp` : eigensystem of the Laplacian
* `heatInner` : `Re⟨f, K_t f⟩ = Σ_k e^{-tλ_k} |c_k|²`

## Main results

* `heat_kernel_psd` : `Re⟨f, K_t f⟩ ≥ 0` for `t ≥ 0`
* `contraction` : `Re⟨f, K_t f⟩ ≤ ‖f‖²`
* `correlator_decay` : `Re⟨f, K_t f⟩ ≤ e^{-tλ₁} · ‖f‖²` for `f ⊥ ground state`

## References

* Ben-Shalom, "Spectral Physics", Chapter 7
-/

noncomputable section

open Finset Real

variable (S : RelationalStructure)

namespace SpectralPhysics

/-- Spectral decomposition of the Laplacian on a relational structure.
    In finite dimensions this is a theorem (Mathlib: `Matrix.IsHermitian.spectral_theorem`).
    We axiomatize it on the function space directly. -/
structure SpectralDecomp (S : RelationalStructure) (n : ℕ) where
  /-- Eigenvalues, sorted and non-negative -/
  eigenval : Fin n → ℝ
  eigenval_nonneg : ∀ (k : Fin n), 0 ≤ eigenval k
  eigenval_sorted : ∀ (i j : Fin n), i ≤ j → eigenval i ≤ eigenval j
  /-- Coefficient squared: |c_k(f)|² = Re⟨v_k, f⟩² + Im⟨v_k, f⟩² -/
  coeffSq : (S.X → ℂ) → Fin n → ℝ
  coeffSq_nonneg : ∀ (f : S.X → ℂ) (k : Fin n), 0 ≤ coeffSq f k
  /-- Parseval: ‖f‖² = Σ |c_k|² -/
  parseval : ∀ (f : S.X → ℂ),
    (S.innerProduct f f).re = ∑ k : Fin n, coeffSq f k
  /-- Spectral representation: Re⟨f, Lf⟩ = Σ λ_k |c_k|² -/
  spectral_repr : ∀ (f : S.X → ℂ),
    (S.innerProduct f (S.SpectralLaplacian f)).re =
    ∑ k : Fin n, eigenval k * coeffSq f k

variable {S}

/-- The heat kernel inner product: `Re⟨f, K_t f⟩ = Σ_k e^{-tλ_k} |c_k(f)|²`.
    This is the spectral representation of the Euclidean correlator. -/
def heatInner {n : ℕ} (sd : SpectralDecomp S n) (f : S.X → ℂ) (t : ℝ) : ℝ :=
  ∑ k : Fin n, Real.exp (-t * sd.eigenval k) * sd.coeffSq f k

/-- **Heat kernel PSD**: `Re⟨f, K_t f⟩ ≥ 0` for all `t`.
    Each term `e^{-tλ_k} |c_k|²` is non-negative. -/
theorem heat_kernel_psd {n : ℕ} (sd : SpectralDecomp S n)
    (f : S.X → ℂ) (t : ℝ) :
    0 ≤ heatInner sd f t := by
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (le_of_lt (Real.exp_pos _)) (sd.coeffSq_nonneg f k)

/-- **Contraction**: `Re⟨f, K_t f⟩ ≤ ‖f‖²` for `t ≥ 0`.
    Since `e^{-tλ_k} ≤ 1` when `t ≥ 0` and `λ_k ≥ 0`. -/
theorem contraction {n : ℕ} (sd : SpectralDecomp S n)
    (f : S.X → ℂ) (t : ℝ) (ht : 0 ≤ t) :
    heatInner sd f t ≤ (S.innerProduct f f).re := by
  rw [sd.parseval f]
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_of_le_one_left (sd.coeffSq_nonneg f k)
  rw [Real.exp_le_one_iff]
  nlinarith [sd.eigenval_nonneg k]

/-- **Correlator exponential decay**: For `f` with zero ground-state component,
    `Re⟨f, K_t f⟩ ≤ e^{-tλ₁} · ‖f‖²`.

    This IS the mass gap in Euclidean signature. -/
theorem correlator_decay {n : ℕ} (sd : SpectralDecomp S n)
    (hn : 1 < n)
    (f : S.X → ℂ)
    (hf : sd.coeffSq f ⟨0, by omega⟩ = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    heatInner sd f t ≤
      Real.exp (-t * sd.eigenval ⟨1, hn⟩) * (S.innerProduct f f).re := by
  rw [sd.parseval f]
  unfold heatInner
  -- Goal: Σ e^{-tλ_k} c_k ≤ e^{-tλ₁} · Σ c_k
  -- Factor: e^{-tλ₁} · Σ c_k = Σ e^{-tλ₁} · c_k
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : (k : ℕ) = 0
  · -- k = 0: coefficient vanishes
    have : k = ⟨0, by omega⟩ := Fin.ext (by omega)
    rw [this, hf, mul_zero, mul_zero]
  · -- k ≥ 1: e^{-tλ_k} ≤ e^{-tλ₁} since λ_k ≥ λ₁ and t ≥ 0
    apply mul_le_mul_of_nonneg_right _ (sd.coeffSq_nonneg f k)
    apply Real.exp_le_exp.mpr
    have hle : sd.eigenval ⟨1, hn⟩ ≤ sd.eigenval k :=
      sd.eigenval_sorted ⟨1, hn⟩ k (Nat.one_le_iff_ne_zero.mpr hk)
    nlinarith

/-- The spectral gap gives a mass: `m = √λ₁ > 0`. -/
theorem mass_from_gap {n : ℕ} (sd : SpectralDecomp S n)
    (hn : 1 < n) (h_gap : 0 < sd.eigenval ⟨1, hn⟩) :
    0 < Real.sqrt (sd.eigenval ⟨1, hn⟩) :=
  Real.sqrt_pos_of_pos h_gap

end SpectralPhysics

end
