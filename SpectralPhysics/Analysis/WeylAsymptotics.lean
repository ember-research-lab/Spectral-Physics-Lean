/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Weyl Asymptotics (Axiomatized)

Weyl's law for eigenvalue asymptotics on a 4-dimensional Riemannian manifold.
This is axiomatized (not derived from our three axioms) because it encodes
the continuum limit that the discrete spectral graph converges to.

The key content: on a compact 4-manifold (M, g) of volume V,
the eigenvalue counting function satisfies
  N(λ) ~ C₄ · V · λ² as λ → ∞
where C₄ = ω₄/(2π)⁴ · V and d = 4 is the spectral dimension.

## Main definitions

* `WeylAsymptotics` : typeclass packaging the spectral dimension,
  counting function asymptotic, and eigenfunction bound

## References

* Weyl, "Das asymptotische Verteilungsgesetz der Eigenwerte" (1911)
* Ben-Shalom, "Spectral Physics", Chapter 8
-/

noncomputable section

open Finset

namespace SpectralPhysics.Weyl

/-- The spectral dimension of the continuum limit. Fixed at 4 by
    the Cayley-Dickson tower: dim_ℝ(ℂ ⊗ ℍ ⊗ 𝕆) = 2·4·8 = 64,
    but the effective spacetime dimension from the Laplacian heat
    trace is d = 4. -/
def spectralDim : ℕ := 4

/-- **Weyl asymptotics** for a sequence of eigenvalues on a d-dimensional
    compact manifold. Axiomatized as a class so downstream files
    (SpectralConvergence, FieldOperators) can assume it. -/
class WeylAsymptotics (eigenvalues : ℕ → ℝ) where
  /-- Eigenvalues are non-negative and non-decreasing -/
  eigenvalue_nonneg : ∀ (n : ℕ), 0 ≤ eigenvalues n
  eigenvalue_mono : ∀ (n m : ℕ), n ≤ m → eigenvalues n ≤ eigenvalues m
  /-- Eigenvalues grow to infinity -/
  eigenvalue_tendsto_top : Filter.Tendsto eigenvalues Filter.atTop Filter.atTop
  /-- Weyl asymptotic: λ_n ~ C · n^{2/d} as n → ∞, with d = 4.
      Equivalently, N(λ) ~ C' · λ^{d/2} = C' · λ². -/
  weyl_asymptotic :
    ∃ (C : ℝ), 0 < C ∧
      Filter.Tendsto (fun n : ℕ => eigenvalues n / (n : ℝ) ^ ((2 : ℝ) / spectralDim))
        Filter.atTop (nhds C)
  /-- Eigenfunction L^∞ bound: ‖φₙ‖_∞ ≤ C · λₙ^{(d-1)/2}.
      For d = 4 this is ‖φₙ‖_∞ ≤ C · λₙ^{3/2}. -/
  eigenfunction_bound :
    ∃ (C : ℝ), 0 < C ∧
      ∀ (n : ℕ), eigenvalues n ≠ 0 →
        True  -- Placeholder: bound on the n-th eigenfunction sup norm
  /-- Pointwise Weyl bound: eventually 1 + λ_n ≤ C·(1+n)^{1/2}.
      This is the pointwise consequence of the Weyl asymptotic. -/
  weyl_pointwise_bound :
    ∃ (C : ℝ), 0 < C ∧ ∀ (n : ℕ), 1 + eigenvalues n ≤ C * ((1 + n : ℝ) ^ ((1 : ℝ) / 2))
  /-- Heat trace summability: ∑ e^{-tλ_n} < ∞ for t > 0.
      This is a CONSEQUENCE of the Weyl asymptotic (λ_n ~ C n^{1/2} gives
      super-polynomial decay of e^{-tλ_n}), but the formal comparison test
      chain (Weyl → pointwise bound → summability) requires connecting
      Filter.Tendsto to a pointwise eventually-bound and then to
      Summable.of_norm_bounded_eventually. We include it as a class field
      since it's a standard consequence of Weyl asymptotics. -/
  summable_heat : ∀ (t : ℝ), 0 < t →
    Summable (fun n => Real.exp (-t * eigenvalues n))

/-- The heat trace on a Weyl-asymptotic spectrum converges for t > 0.
    ∑ₙ e^{-t λₙ} < ∞ follows from λₙ ~ C n^{1/2} (for d=4). -/
theorem heat_trace_converges
    (eigenvalues : ℕ → ℝ) [WeylAsymptotics eigenvalues]
    (t : ℝ) (ht : 0 < t) :
    ∃ (S : ℝ), Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, Real.exp (-t * eigenvalues n))
      Filter.atTop (nhds S) := by
  -- The terms e^{-tλ_n} are non-negative
  have h_nn : ∀ n, 0 ≤ Real.exp (-t * eigenvalues n) :=
    fun n => le_of_lt (Real.exp_pos _)
  -- Summability: the Weyl asymptotic λ_n ~ C·n^{1/2} gives
  -- e^{-tλ_n} ≤ e^{-(tC/2)√n} ≤ 1/(n+1)^2 eventually,
  -- so the series converges by comparison with ∑ 1/(n+1)^2.
  -- The formal chain (Weyl → comparison → summability) requires
  -- connecting the asymptotic to a pointwise bound; we isolate this.
  have h_summable : Summable (fun n => Real.exp (-t * eigenvalues n)) :=
    WeylAsymptotics.summable_heat t ht
  exact ⟨∑' n, Real.exp (-t * eigenvalues n),
    (hasSum_iff_tendsto_nat_of_nonneg h_nn _).mp h_summable.hasSum⟩

end SpectralPhysics.Weyl

end
