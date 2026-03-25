/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Axioms.RelationalStructure

/-!
# Sign Change Lemma

A nonzero function with zero weighted sum must change sign.
This is the key property of the Fiedler vector.

## Main results

* `sign_change` : Σ f(x)·w(x) = 0, f ≠ 0, w > 0 ⟹ f changes sign
-/

open Finset

namespace SpectralPhysics.SignChange

/-- A nonzero function with zero weighted sum (positive weights) must
take both positive and negative values. -/
theorem sign_change (S : RelationalStructure)
    (f : S.X → ℝ)
    (h_nonzero : ∃ x : S.X, f x ≠ 0)
    (h_sum : ∑ x : S.X, f x * S.μ x = 0) :
    (∃ x : S.X, 0 < f x) ∧ (∃ y : S.X, f y < 0) := by
  constructor
  · -- If all f(x) ≤ 0 and some f(x₀) ≠ 0:
    -- f(x₀) < 0, so f(x₀)·μ(x₀) < 0, and all other terms ≤ 0.
    -- Sum < 0, contradicting h_sum = 0.
    by_contra h
    push_neg at h  -- h : ∀ x, f x ≤ 0
    obtain ⟨x₀, hx₀⟩ := h_nonzero
    have hx₀_neg : f x₀ < 0 := lt_of_le_of_ne (h x₀) hx₀
    have h_term_neg : f x₀ * S.μ x₀ < 0 := mul_neg_of_neg_of_pos hx₀_neg (S.μ_pos x₀)
    have h_le_term : ∑ x : S.X, f x * S.μ x ≤ f x₀ * S.μ x₀ := by
      have h_rest : ∑ x ∈ Finset.univ.erase x₀, f x * S.μ x ≤ 0 :=
        Finset.sum_nonpos fun x _ => mul_nonpos_of_nonpos_of_nonneg (h x) (le_of_lt (S.μ_pos x))
      linarith [Finset.add_sum_erase Finset.univ (fun x => f x * S.μ x) (Finset.mem_univ x₀)]
    linarith
  · -- Symmetric: if all f(x) ≥ 0, sum > 0, contradiction.
    by_contra h
    push_neg at h  -- h : ∀ y, 0 ≤ f y
    obtain ⟨x₀, hx₀⟩ := h_nonzero
    have hx₀_pos : 0 < f x₀ := lt_of_le_of_ne (h x₀) (Ne.symm hx₀)
    have h_term_pos : 0 < f x₀ * S.μ x₀ := mul_pos hx₀_pos (S.μ_pos x₀)
    have h_ge_term : f x₀ * S.μ x₀ ≤ ∑ x : S.X, f x * S.μ x :=
      Finset.single_le_sum (fun x _ => mul_nonneg (h x) (le_of_lt (S.μ_pos x)))
        (Finset.mem_univ x₀)
    linarith

end SpectralPhysics.SignChange
