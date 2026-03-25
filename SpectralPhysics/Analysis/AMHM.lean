/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# AM-HM Inequality via Cauchy-Schwarz

The AM-HM inequality: for positive reals a_1,...,a_n,
  (Σ 1/a_k)(Σ a_k) ≥ n².

This is Cauchy-Schwarz with f_k = 1/√a_k, g_k = √a_k:
  (Σ f_k g_k)² ≤ (Σ f_k²)(Σ g_k²)
  (Σ 1)² ≤ (Σ 1/a_k)(Σ a_k)
  n² ≤ (Σ 1/a_k)(Σ a_k).

## Main results

* `sum_inv_mul_sum_ge_sq` : (Σ 1/a_k)(Σ a_k) ≥ n²
-/

noncomputable section

open Finset Real

namespace SpectralPhysics.AMHM

/-- **AM-HM inequality**: (Σ 1/a_k)(Σ a_k) ≥ n² for positive reals.

Proof via Cauchy-Schwarz: set f_k = 1/√a_k, g_k = √a_k.
Then f_k · g_k = 1, f_k² = 1/a_k, g_k² = a_k.
Cauchy-Schwarz: (Σ f·g)² ≤ (Σ f²)(Σ g²) gives n² ≤ (Σ 1/a)(Σ a). -/
theorem sum_inv_mul_sum_ge_sq {n : ℕ} (a : Fin n → ℝ) (ha : ∀ k, 0 < a k)
    (hn : 0 < n) :
    (n : ℝ) ^ 2 ≤ (∑ k : Fin n, 1 / a k) * (∑ k : Fin n, a k) := by
  -- Use Mathlib's Cauchy-Schwarz: (Σ f·g)² ≤ (Σ f²)(Σ g²)
  -- with f_k = √(1/a_k), g_k = √(a_k)
  let f : Fin n → ℝ := fun k => Real.sqrt (1 / a k)
  let g : Fin n → ℝ := fun k => Real.sqrt (a k)
  have h_cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  -- h_cs : (Σ f·g)² ≤ (Σ f²)(Σ g²)
  -- f·g = √(1/a) · √a = √(1/a · a) = √1 = 1
  have h_fg : ∀ k : Fin n, f k * g k = 1 := by
    intro k
    simp only [f, g]
    rw [← Real.sqrt_mul (le_of_lt (div_pos one_pos (ha k))), one_div,
        inv_mul_cancel₀ (ne_of_gt (ha k)), Real.sqrt_one]
  -- f² = 1/a
  have h_fsq : ∀ k : Fin n, f k ^ 2 = 1 / a k := by
    intro k
    simp only [f]
    rw [Real.sq_sqrt (le_of_lt (div_pos one_pos (ha k)))]
  -- g² = a
  have h_gsq : ∀ k : Fin n, g k ^ 2 = a k := by
    intro k
    simp only [g]
    rw [Real.sq_sqrt (le_of_lt (ha k))]
  -- Rewrite CS using these
  have h1 : ∑ k : Fin n, f k * g k = ∑ k : Fin n, (1 : ℝ) := by
    congr 1; ext k; exact h_fg k
  have h2 : ∑ k : Fin n, f k ^ 2 = ∑ k : Fin n, 1 / a k := by
    congr 1; ext k; exact h_fsq k
  have h3 : ∑ k : Fin n, g k ^ 2 = ∑ k : Fin n, a k := by
    congr 1; ext k; exact h_gsq k
  rw [h1, h2, h3] at h_cs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h_cs
  linarith

end SpectralPhysics.AMHM

end
