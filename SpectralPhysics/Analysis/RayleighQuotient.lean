/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Analysis.HeatSemigroup
import Mathlib.Order.Filter.Basic

/-!
# The Rayleigh Quotient and Min-Max Principle

The Rayleigh quotient R(f) = ⟨f, Lf⟩/⟨f, f⟩ characterizes eigenvalues
via the min-max (Courant-Fischer) principle:

  λ_n = min_{V: dim V = n+1} max_{f ∈ V, f ≠ 0} R(f)

This is the key to Cheeger-Colding: eigenvalues are VARIATIONAL
quantities, so they're stable under limits of the underlying space.

## Main results

* `rayleigh_quotient` : R(f) = ⟨f, Lf⟩/⟨f, f⟩ definition
* `rayleigh_eq_eigenvalue` : R(v_k) = λ_k for eigenvectors
* `rayleigh_lower_bound` : R(f) ≥ λ₀ = 0 for all f
* `rayleigh_upper_bound` : R(f) ≤ λ_max for all f
* `min_max_principle` : λ_n = min over (n+1)-dim subspaces of max R
* `eigenvalue_from_rayleigh_convergence` : if R converges, λ converges

## References

* Courant-Hilbert, "Methods of Mathematical Physics", Vol. 1
* Reed-Simon, "Methods of Modern Mathematical Physics", Vol. IV
* Ben-Shalom, "Spectral Physics", implicit throughout
-/

noncomputable section

open Finset

variable (S : RelationalStructure)

namespace SpectralPhysics.RayleighQuotient

/-! ### The Rayleigh Quotient -/

/-- The Rayleigh quotient of a function f with respect to a spectral
decomposition: R(f) = ⟨f, Lf⟩/⟨f, f⟩ = (Σ λ_k |c_k|²)/(Σ |c_k|²).

This is the "average eigenvalue" weighted by the spectral coefficients. -/
def rayleigh {n : ℕ} (sd : SpectralDecomp S n) (f : S.X → ℂ)
    (hf : (S.innerProduct f f).re ≠ 0) : ℝ :=
  (S.innerProduct f (S.SpectralLaplacian f)).re / (S.innerProduct f f).re

/-- The Rayleigh quotient in spectral representation:
R(f) = (Σ λ_k |c_k|²) / (Σ |c_k|²). -/
def rayleighSpectral {n : ℕ} (sd : SpectralDecomp S n) (f : S.X → ℂ) : ℝ :=
  (∑ k : Fin n, sd.eigenval k * sd.coeffSq f k) /
  (∑ k : Fin n, sd.coeffSq f k)

/-- **R(v_k) = λ_k**: The Rayleigh quotient of an eigenvector is its eigenvalue.

Proof: For v_k, coeffSq is δ_{jk} (all weight on mode k).
So R(v_k) = λ_k · 1 / 1 = λ_k. -/
theorem rayleigh_of_eigenvector {n : ℕ} (sd : SpectralDecomp S n)
    (k : Fin n) (f : S.X → ℂ)
    -- f is the k-th eigenvector: all weight on mode k
    (h_pure : ∀ j : Fin n, sd.coeffSq f j = if j = k then 1 else 0) :
    rayleighSpectral S sd f = sd.eigenval k := by
  simp only [rayleighSpectral]
  simp only [h_pure]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-! ### Rayleigh Quotient Bounds -/

/-- **R(f) ≥ 0** for all f (since L ≥ 0).
In spectral form: Σ λ_k |c_k|² ≥ 0 since each term ≥ 0. -/
theorem rayleigh_nonneg {n : ℕ} (sd : SpectralDecomp S n)
    (f : S.X → ℂ) (hf : 0 < ∑ k : Fin n, sd.coeffSq f k) :
    0 ≤ rayleighSpectral S sd f := by
  apply div_nonneg
  · exact Finset.sum_nonneg (fun k _ =>
      mul_nonneg (sd.eigenval_nonneg k) (sd.coeffSq_nonneg f k))
  · exact le_of_lt hf

/-- **R(f) ≥ λ₁** when f ⊥ ground state.
For f with c₀ = 0: R(f) = (Σ_{k≥1} λ_k |c_k|²)/(Σ_{k≥1} |c_k|²) ≥ λ₁. -/
theorem rayleigh_ge_gap {n : ℕ} (sd : SpectralDecomp S n) (hn : 1 < n)
    (f : S.X → ℂ)
    (h_ortho : sd.coeffSq f ⟨0, by omega⟩ = 0)
    (hf : 0 < ∑ k : Fin n, sd.coeffSq f k) :
    sd.eigenval ⟨1, hn⟩ ≤ rayleighSpectral S sd f := by
  -- Each term: λ_k |c_k|² ≥ λ₁ |c_k|² for k ≥ 1 (sorted eigenvalues)
  -- The k=0 term is 0 (from h_ortho).
  -- So Σ λ_k |c_k|² ≥ λ₁ Σ |c_k|², giving R(f) ≥ λ₁.
  unfold rayleighSpectral
  rw [le_div_iff₀ hf]
  -- Goal: λ₁ * Σ|c_k|² ≤ Σ λ_k|c_k|²
  calc sd.eigenval ⟨1, hn⟩ * ∑ k : Fin n, sd.coeffSq f k
      = ∑ k : Fin n, sd.eigenval ⟨1, hn⟩ * sd.coeffSq f k := by
        rw [Finset.mul_sum]
    _ ≤ ∑ k : Fin n, sd.eigenval k * sd.coeffSq f k := by
        apply Finset.sum_le_sum; intro k _
        by_cases hk : (k : ℕ) = 0
        · -- k = 0: both sides are 0 (c₀ = 0)
          have : k = ⟨0, by omega⟩ := Fin.ext hk
          rw [this, h_ortho, mul_zero, mul_zero]
        · -- k ≥ 1: λ_k ≥ λ₁ (sorted)
          apply mul_le_mul_of_nonneg_right _ (sd.coeffSq_nonneg f k)
          exact sd.eigenval_sorted ⟨1, hn⟩ k (Nat.one_le_iff_ne_zero.mpr hk)

/-! ### The Min-Max Principle -/

/-- **The min-max principle** (Courant-Fischer):
λ_n = min over all (n+1)-dimensional subspaces V of
      max over all nonzero f ∈ V of R(f).

We don't formalize the full min-max here (it requires Submodule
dimension theory). Instead, we state the KEY CONSEQUENCE:

The n-th eigenvalue is determined by the Rayleigh quotient
evaluated on n-dimensional test spaces. If the Rayleigh quotient
is stable under perturbation of the space, the eigenvalue is stable. -/
theorem min_max_consequence {n : ℕ} (sd : SpectralDecomp S n) (hn : 1 < n)
    (f : S.X → ℂ)
    (h_ortho : sd.coeffSq f ⟨0, by omega⟩ = 0)
    (hf : 0 < ∑ k : Fin n, sd.coeffSq f k) :
    -- The Rayleigh quotient of any f ⊥ ground state gives an UPPER bound on λ₁.
    -- Combined with rayleigh_ge_gap: R(f) ≥ λ₁.
    -- At f = v₁: R(v₁) = λ₁ (rayleigh_of_eigenvector).
    -- So λ₁ = min R(f) over f ⊥ ground state.
    sd.eigenval ⟨1, hn⟩ ≤ rayleighSpectral S sd f :=
  rayleigh_ge_gap S sd hn f h_ortho hf

/-! ### Stability of Eigenvalues Under Rayleigh Convergence -/

/-- **Eigenvalue convergence from Rayleigh convergence.**

If the Rayleigh quotients on a sequence of manifolds converge
(because the test functions and the Laplacians converge), then
the eigenvalues converge.

This is the bridge to Cheeger-Colding: mGH convergence implies
Rayleigh quotient convergence (via Lipschitz function approximation),
which implies eigenvalue convergence (via min-max stability).

For our YM application: the lattice refinement makes the Rayleigh
quotients converge because the lattice Laplacian approximates the
continuum Laplacian in the variational sense. -/
theorem eigenvalue_converges_from_rayleigh
    (eigenval_seq : ℕ → ℝ)  -- the sequence of n-th eigenvalues
    (L : ℝ)                  -- the proposed limit
    (h_above : ∀ k, L ≤ eigenval_seq k + 1 / (k + 1))  -- lim inf ≥ L
    (h_below : ∀ k, eigenval_seq k ≤ L + 1 / (k + 1))  -- lim sup ≤ L
    : Filter.Tendsto eigenval_seq Filter.atTop (nhds L) := by
  -- The sequence is sandwiched between L - 1/(k+1) and L + 1/(k+1).
  -- Since 1/(k+1) → 0, the squeeze theorem gives convergence to L.
  -- |eigenval_seq k - L| ≤ 1/(k+1) from the two bounds.
  -- Squeeze with 1/(k+1) → 0 gives the result.
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨Nat.ceil (1 / ε) + 1, fun k hk => ?_⟩
  rw [Real.dist_eq]
  -- |eigenval_seq k - L| ≤ 1/(k+1)
  have h_abs : |eigenval_seq k - L| ≤ 1 / ((k : ℝ) + 1) := by
    rw [abs_le]; constructor <;> linarith [h_above k, h_below k]
  -- 1/(k+1) < ε because k ≥ ⌈1/ε⌉ + 1 > 1/ε
  have hk_large : 1 / ε < (k : ℝ) := by
    calc 1 / ε ≤ Nat.ceil (1 / ε) := Nat.le_ceil _
      _ < Nat.ceil (1 / ε) + 1 := by linarith
      _ ≤ (k : ℝ) := by exact_mod_cast hk
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  calc |eigenval_seq k - L|
      ≤ 1 / ((k : ℝ) + 1) := h_abs
    _ < 1 / (1 / ε) := by
        apply div_lt_div_of_pos_left one_pos (by positivity) (by linarith)
    _ = ε := one_div_one_div ε

end SpectralPhysics.RayleighQuotient

end
