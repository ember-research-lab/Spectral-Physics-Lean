import SpectralPhysics.Thermo.FourLaws
import Mathlib.Analysis.Complex.ExponentialBounds
open SpectralPhysics.Thermo Finset

noncomputable def badpop (t : ℝ) (k : Fin 2) : ℝ :=
  if t < 1 then 1/2 else (if k = 0 then 9/10 else 1/10)

theorem badpop_pos : ∀ t k, 0 < badpop t k := by
  intro t k; unfold badpop; split_ifs <;> norm_num

theorem badpop_1_0 : badpop 1 0 = 9/10 := by simp [badpop]
theorem badpop_1_1 : badpop 1 1 = 1/10 := by simp [badpop]
theorem badpop_0_k (k : Fin 2) : badpop 0 k = 1/2 := by simp [badpop]

theorem badpop_sum : ∀ t, ∑ k : Fin 2, badpop t k = 1 := by
  intro t; simp only [Fin.sum_univ_two, badpop]
  by_cases h : t < 1
  · rw [if_pos h, if_pos h]; norm_num
  · rw [if_neg h, if_neg h]; simp; norm_num

theorem entropy_claim :
    ∑ k : Fin 2, -(badpop 0 k * Real.log (badpop 0 k)) ≤
    ∑ k : Fin 2, -(badpop 1 k * Real.log (badpop 1 k)) :=
  second_law_entropy_increase (fun _ => 0) (fun _ => le_refl 0) badpop badpop_pos badpop_sum
    trivial 0 1 le_rfl zero_le_one

theorem lhs_val : ∑ k : Fin 2, -(badpop 0 k * Real.log (badpop 0 k)) = Real.log 2 := by
  simp only [Fin.sum_univ_two, badpop_0_k]
  have : Real.log (1/2 : ℝ) = - Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [this]; ring

theorem rhs_val : ∑ k : Fin 2, -(badpop 1 k * Real.log (badpop 1 k))
    = -(9/10 * Real.log (9/10)) - 1/10 * Real.log (1/10) := by
  simp only [Fin.sum_univ_two, badpop_1_0, badpop_1_1]; ring

theorem log10_le : Real.log 10 ≤ 2.4 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : Real.exp 2.4 = Real.exp 1 * Real.exp 1 * Real.exp 0.4 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h04 : (1.4 : ℝ) ≤ Real.exp 0.4 := by
    have := Real.add_one_le_exp (0.4 : ℝ); linarith
  rw [h1]
  have hp : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  nlinarith [mul_pos hp hp, Real.exp_pos (0.4:ℝ)]

theorem derive_false : False := by
  have h := entropy_claim
  rw [lhs_val, rhs_val] at h
  have h2 : Real.log 2 > 0.69 := by have := Real.log_two_gt_d9; linarith
  have h9 : -(1/9 : ℝ) ≤ Real.log (9/10) := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 9/10)
    norm_num at this ⊢; linarith
  have h1 : Real.log (1/10 : ℝ) = - Real.log 10 := by rw [one_div, Real.log_inv]
  rw [h1] at h
  have := log10_le
  linarith
