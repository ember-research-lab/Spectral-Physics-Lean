/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Complex Exponential Lemmas

Helper lemmas for `Complex.exp` on purely imaginary arguments.
Used by QuantumMechanics.lean and Propagator.lean.

## Main results

* `normSq_exp_imaginary` : `normSq(exp(iθ)) = 1` for real θ
* `normSq_exp_neg_imaginary` : `normSq(exp(-iθ)) = 1`
-/

noncomputable section

open Complex

namespace SpectralPhysics.ComplexExp

/-- `‖exp(θ·I)‖ = 1` for real θ. This is `norm_exp_ofReal_mul_I` from Mathlib. -/
theorem norm_exp_pure_imaginary (θ : ℝ) : ‖exp ((θ : ℂ) * I)‖ = 1 :=
  norm_exp_ofReal_mul_I θ

/-- `normSq(exp(θ·I)) = 1` for real θ.
Follows from ‖z‖² = normSq(z) and ‖exp(θI)‖ = 1. -/
-- Bridge: normSq z = ‖z‖² for complex numbers.
-- From Complex.norm_def: ‖z‖ = √(normSq z), so ‖z‖² = normSq z.
private theorem normSq_eq_norm_sq (z : ℂ) : normSq z = ‖z‖ ^ 2 := by
  rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg z)]

theorem normSq_exp_pure_imaginary (θ : ℝ) :
    normSq (exp ((θ : ℂ) * I)) = 1 := by
  rw [normSq_eq_norm_sq, norm_exp_pure_imaginary, one_pow]

/-- `normSq(exp(-I·a·t)) = 1` for real a, t.
The exponent -I·a·t = -(a·t)·I is purely imaginary. -/
theorem normSq_exp_neg_I_mul (a t : ℝ) :
    normSq (exp (-I * (a : ℂ) * (t : ℂ))) = 1 := by
  have h : -I * (a : ℂ) * (t : ℂ) = (↑(-(a * t)) : ℂ) * I := by push_cast; ring
  rw [h]; exact normSq_exp_pure_imaginary _

end SpectralPhysics.ComplexExp

end
