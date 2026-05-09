/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.YukawaHierarchy.Bundle.THooftSymbol
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# BPST Instanton Curvature 2-Form

The Belavin-Polyakov-Schwarz-Tyupkin (BPST) 1-instanton on R⁴ ⊂ S⁴, in
the SU(2) fundamental representation, has gauge field

  `A^a_μ(x) = 2 η^a_{μν} x^ν / (x² + ρ²)`

with curvature

  `F^a_{μν}(x) = -4 ρ² η^a_{μν} / (x² + ρ²)²`.

This file formalizes the curvature `F^a_{μν}(x)` as a real-valued
function and proves antisymmetry, diagonal vanishing, and self-duality
(Tier 1).

## Tier classification

* **Tier 1 (proved)**: antisymmetry, diagonal vanishing, self-duality
  pointwise.
* **Tier 3 (deferred)**: integrating over `R⁴` to get the topological
  charge. That requires Mathlib `MeasureTheory.Integral` machinery —
  not needed for the algebraic content, and lives in
  `Bundle/InstantonNumber.lean`.

## References

* Belavin, A.A., Polyakov, A.M., Schwartz, A.S., Tyupkin, Y.S. (1975).
  "Pseudoparticle solutions of the Yang-Mills equations."
  Phys. Lett. B 59, 85.
* Coleman, S. (1985). *Aspects of Symmetry*, Chapter 7.
-/

namespace SpectralPhysics.YukawaHierarchy.Bundle

open scoped BigOperators

/-! ## The squared norm of a 4-vector -/

/-- `|x|² = x_0² + x_1² + x_2² + x_3²` for `x : Fin 4 → ℝ`. -/
def normSq (x : Fin 4 → ℝ) : ℝ := ∑ μ : Fin 4, x μ * x μ

/-- The squared norm is non-negative. -/
theorem normSq_nonneg (x : Fin 4 → ℝ) : 0 ≤ normSq x := by
  unfold normSq
  apply Finset.sum_nonneg
  intro μ _
  exact mul_self_nonneg _

/-! ## The BPST curvature 2-form -/

/-- The BPST curvature 2-form `F^a_{μν}(x)` on `R⁴`, in the fundamental
    representation of SU(2), with instanton scale `ρ`.

      `F^a_{μν}(x) = -4 ρ² η^a_{μν} / (x² + ρ²)²`. -/
noncomputable def BPSTField (ρ : ℝ) (x : Fin 4 → ℝ)
    (a : Fin 3) (μ ν : Fin 4) : ℝ :=
  -4 * ρ^2 * (tHooftEta a μ ν : ℝ) / (normSq x + ρ^2)^2

/-! ## Tier-1 properties -/

/-- The denominator `(x² + ρ²)²` is positive when `ρ ≠ 0`. -/
theorem BPST_denom_pos (ρ : ℝ) (x : Fin 4 → ℝ) (hρ : ρ ≠ 0) :
    0 < (normSq x + ρ^2)^2 := by
  have h1 : 0 ≤ normSq x := normSq_nonneg x
  have h2 : 0 < ρ^2 := by positivity
  have h_inner : 0 < normSq x + ρ^2 := by linarith
  positivity

/-- **Tier 1.**  Antisymmetry of the BPST curvature in `(μ, ν)`. -/
theorem BPSTField_antisym (ρ : ℝ) (x : Fin 4 → ℝ) (a : Fin 3) (μ ν : Fin 4) :
    BPSTField ρ x a μ ν = -BPSTField ρ x a ν μ := by
  unfold BPSTField
  have h_int : tHooftEta a μ ν = -tHooftEta a ν μ := tHooftEta_antisym a μ ν
  have h_real : (tHooftEta a μ ν : ℝ) = -(tHooftEta a ν μ : ℝ) := by
    have : ((tHooftEta a μ ν : ℤ) : ℝ) = ((-tHooftEta a ν μ : ℤ) : ℝ) := by
      exact_mod_cast h_int
    simpa using this
  rw [h_real]; ring

/-- **Tier 1.**  Diagonal vanishing: `F^a_{μμ}(x) = 0`. -/
theorem BPSTField_diag (ρ : ℝ) (x : Fin 4 → ℝ) (a : Fin 3) (μ : Fin 4) :
    BPSTField ρ x a μ μ = 0 := by
  unfold BPSTField
  have h_int : tHooftEta a μ μ = 0 := tHooftEta_diag a μ
  have h_real : (tHooftEta a μ μ : ℝ) = 0 := by exact_mod_cast h_int
  rw [h_real]; ring

/-! ## Self-duality

The BPST curvature is self-dual: `F = ★F`, equivalently

  `Σ_{ρσ} ε_{μνρσ} F^a_{ρσ}(x) = 2 F^a_{μν}(x)`. -/

/-- Helper: the constant prefactor of the BPST curvature is independent of
    the spacetime indices. -/
private noncomputable def bpstPrefactor (ρ : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  -4 * ρ^2 / (normSq x + ρ^2)^2

private theorem BPSTField_eq_prefactor_times_eta
    (ρ : ℝ) (x : Fin 4 → ℝ) (a : Fin 3) (μ ν : Fin 4) :
    BPSTField ρ x a μ ν
    = bpstPrefactor ρ x * (tHooftEta a μ ν : ℝ) := by
  unfold BPSTField bpstPrefactor; ring

/-- **Tier 1.**  Self-duality of the BPST curvature.

    The eta-side identity `Σ ε · η = 2 η` (proved by `decide` in
    `tHooftEta_selfDual`) lifts to a Real-valued identity by casting,
    and then we factor the constant prefactor `-4 ρ² / (x² + ρ²)²` out
    of the sum. -/
theorem BPSTField_selfDual
    (ρ_scale : ℝ) (x : Fin 4 → ℝ) (a : Fin 3) (μ ν : Fin 4) :
    (∑ ρ : Fin 4, ∑ σ : Fin 4,
      (epsilon4 μ ν ρ σ : ℝ) * BPSTField ρ_scale x a ρ σ)
    = 2 * BPSTField ρ_scale x a μ ν := by
  -- Replace each F summand by C · ε · η.
  set C : ℝ := bpstPrefactor ρ_scale x with hCdef
  have h_F : ∀ ρ σ : Fin 4,
      (epsilon4 μ ν ρ σ : ℝ) * BPSTField ρ_scale x a ρ σ
      = C * ((epsilon4 μ ν ρ σ : ℝ) * (tHooftEta a ρ σ : ℝ)) := by
    intro ρ σ
    rw [BPSTField_eq_prefactor_times_eta]; ring
  simp_rw [h_F]
  -- Factor C out of the double sum (manual: rewrite via Finset.sum_congr is easier)
  have hF1 : ∀ ρ : Fin 4,
      (∑ σ : Fin 4, C * ((epsilon4 μ ν ρ σ : ℝ) * (tHooftEta a ρ σ : ℝ)))
      = C * (∑ σ : Fin 4, (epsilon4 μ ν ρ σ : ℝ) * (tHooftEta a ρ σ : ℝ)) := by
    intro ρ; rw [← Finset.mul_sum]
  simp_rw [hF1]
  rw [← Finset.mul_sum]
  -- Now: C * Σ ε · η = 2 · F. Use the integer self-duality h_eta.
  have h_eta := tHooftEta_selfDual a μ ν
  have h_eta_real :
      (∑ ρ : Fin 4, ∑ σ : Fin 4,
        (epsilon4 μ ν ρ σ : ℝ) * (tHooftEta a ρ σ : ℝ))
      = 2 * (tHooftEta a μ ν : ℝ) := by
    have h_cast :
        ((∑ ρ : Fin 4, ∑ σ : Fin 4,
          epsilon4 μ ν ρ σ * tHooftEta a ρ σ : ℤ) : ℝ)
        = ((2 * tHooftEta a μ ν : ℤ) : ℝ) := by exact_mod_cast h_eta
    push_cast at h_cast
    exact h_cast
  rw [h_eta_real]
  -- Goal: C * (2 · η) = 2 · F
  rw [BPSTField_eq_prefactor_times_eta, hCdef]
  ring

/-! ## The squared density (algebraic content)

For the Pontryagin/topological-charge integral, the integrand is

  `Σ_{a, μ, ν} (F^a_{μν}(x))² = 16 ρ⁴ · Σ_{a, μ, ν} (η^a_{μν})² / (x²+ρ²)⁴
                              = 192 ρ⁴ / (x²+ρ²)⁴`,

using `tHooftEta_total_sumsq = 12`. The formal proof is straightforward
once we factor the constant out of the triple sum. -/

/-- Pointwise sum of squared field components: `Σ_{aμν} (F^a_{μν}(x))²`. -/
noncomputable def BPSTField_sumsq (ρ : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ∑ a : Fin 3, ∑ μ : Fin 4, ∑ ν : Fin 4, (BPSTField ρ x a μ ν)^2

/-- The squared sum is non-negative. -/
theorem BPSTField_sumsq_nonneg (ρ_scale : ℝ) (x : Fin 4 → ℝ) :
    0 ≤ BPSTField_sumsq ρ_scale x := by
  unfold BPSTField_sumsq
  apply Finset.sum_nonneg; intro a _
  apply Finset.sum_nonneg; intro μ _
  apply Finset.sum_nonneg; intro ν _
  exact sq_nonneg _

/-- **Tier 1.**  Closed form of the squared field-strength sum:

      `Σ_{a, μ, ν} (F^a_{μν}(x))² = 192 ρ⁴ / (x² + ρ²)⁴`. -/
theorem BPSTField_sumsq_eq (ρ_scale : ℝ) (x : Fin 4 → ℝ) :
    BPSTField_sumsq ρ_scale x
    = 192 * ρ_scale^4 / (normSq x + ρ_scale^2)^4 := by
  unfold BPSTField_sumsq
  -- Rewrite each summand: (C · η)² = C² · η²
  set C : ℝ := bpstPrefactor ρ_scale x with hCdef
  have h_F : ∀ a : Fin 3, ∀ μ ν : Fin 4,
      (BPSTField ρ_scale x a μ ν)^2
      = C^2 * ((tHooftEta a μ ν : ℝ))^2 := by
    intro a μ ν
    rw [BPSTField_eq_prefactor_times_eta]; ring
  simp_rw [h_F]
  -- Factor C² out of the triple sum
  have h1 : ∀ a : Fin 3, ∀ μ : Fin 4,
      (∑ ν : Fin 4, C^2 * ((tHooftEta a μ ν : ℝ))^2)
      = C^2 * (∑ ν : Fin 4, ((tHooftEta a μ ν : ℝ))^2) := by
    intro a μ; rw [← Finset.mul_sum]
  simp_rw [h1]
  have h2 : ∀ a : Fin 3,
      (∑ μ : Fin 4, C^2 * (∑ ν : Fin 4, ((tHooftEta a μ ν : ℝ))^2))
      = C^2 * (∑ μ : Fin 4, ∑ ν : Fin 4, ((tHooftEta a μ ν : ℝ))^2) := by
    intro a; rw [← Finset.mul_sum]
  simp_rw [h2]
  rw [← Finset.mul_sum]
  -- Σ_aμν η² = 12 (cast from ℤ)
  have h_eta_total :
      (∑ a : Fin 3, ∑ μ : Fin 4, ∑ ν : Fin 4, ((tHooftEta a μ ν : ℝ))^2) = 12 := by
    have hint :
        (∑ a : Fin 3, ∑ μ : Fin 4, ∑ ν : Fin 4, (tHooftEta a μ ν)^2 : ℤ) = 12 :=
      tHooftEta_total_sumsq
    have h_cast :
        ((∑ a : Fin 3, ∑ μ : Fin 4, ∑ ν : Fin 4, (tHooftEta a μ ν)^2 : ℤ) : ℝ)
        = ((12 : ℤ) : ℝ) := by exact_mod_cast hint
    push_cast at h_cast
    exact h_cast
  rw [h_eta_total]
  -- Goal: C² · 12 = 192 ρ⁴ / (x²+ρ²)⁴
  rw [hCdef]
  unfold bpstPrefactor
  -- Use (a/b)² = a²/b² for the prefactor
  rw [div_pow, mul_div_assoc]
  -- LHS: (-4 ρ²)² / ((x²+ρ²)²)² · 12
  -- Use ((x²+ρ²)²)² = (x²+ρ²)⁴
  have h_pow : ((normSq x + ρ_scale^2)^2)^2 = (normSq x + ρ_scale^2)^4 := by ring
  rw [h_pow]
  -- Now: (-4 ρ²)² / (x²+ρ²)⁴ · 12 = 192 ρ⁴ / (x²+ρ²)⁴
  have h_num : ((-4 : ℝ) * ρ_scale^2)^2 = 16 * ρ_scale^4 := by ring
  rw [h_num]
  ring

end SpectralPhysics.YukawaHierarchy.Bundle
