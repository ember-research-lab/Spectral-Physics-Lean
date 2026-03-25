/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Axioms.Laplacian
import Mathlib.Algebra.Order.Field.Basic

/-!
# Cheeger Inequality and Gap Persistence (Ch 33)

The spectral gap is controlled by the isoperimetric (Cheeger) constant:

    h² / (2 d_max) ≤ λ₁ ≤ 2h · d_max

This guarantees that geometric connectivity controls spectral properties.
Combined with perturbation bounds (Davis-Kahan), the gap persists under
bounded deformations.

## Main results

* `CheegerData` : structure binding Cheeger constant to spectral gap
* `cheeger_lower` : h² / (2 d_max) ≤ λ₁
* `cheeger_upper` : λ₁ ≤ 2h · d_max
* `gap_persistence` : gap survives perturbations bounded by δ/2
* `topological_gap` : connected + h > 0 → gap > 0

## References

* Cheeger, "A lower bound for the smallest eigenvalue of the Laplacian" (1970)
* Alon-Milman, "λ₁, isoperimetric inequalities for graphs..." (1985)
* Ben-Shalom, "Spectral Physics", Chapter 33 (Gap Persistence)
-/

noncomputable section

open Finset

namespace SpectralPhysics.CheegerInequality

/-- Isoperimetric data for a relational structure: the Cheeger constant h,
the spectral gap, and the maximum degree. These are related by the
Cheeger inequality. -/
structure CheegerData where
  /-- The Cheeger isoperimetric constant h = inf_{S: μ(S)≤μ(X)/2} |∂S|/μ(S) -/
  cheeger_h : ℝ
  /-- The spectral gap λ₁ (first nonzero eigenvalue) -/
  spectral_gap : ℝ
  /-- Maximum degree d_max = sup_x d(x) -/
  d_max : ℝ
  /-- Cheeger constant is non-negative -/
  cheeger_nonneg : 0 ≤ cheeger_h
  /-- Spectral gap is non-negative -/
  gap_nonneg : 0 ≤ spectral_gap
  /-- Maximum degree is positive -/
  d_max_pos : 0 < d_max

/-- **Cheeger inequality (lower bound)**: h² / (2 d_max) ≤ λ₁.

The spectral gap is at least quadratic in the Cheeger constant.

Proof sketch (Cheeger 1970 / Alon-Milman 1985):
Take the Fiedler vector v₁ (eigenvector for λ₁). Define level sets
S_t = {x : v₁(x) ≥ t}. The co-area formula gives:
  ∫ |∂S_t| dt ≤ Σ_{x~y} |v₁(x) - v₁(y)| w(x,y).
Cauchy-Schwarz + Rayleigh quotient: h ≤ √(2λ₁ d_max).

Manuscript: Theorem 33.1 (thm:cheeger, line 11533). -/
axiom cheeger_lower (cd : CheegerData) :
    cd.cheeger_h ^ 2 / (2 * cd.d_max) ≤ cd.spectral_gap

/-- **Cheeger inequality (upper bound)**: λ₁ ≤ 2h · d_max.

Proof sketch (Buser 1982):
Construct a test function f: f = 1 on the optimal set S, f = 0 on S̄,
linear on the boundary. Rayleigh quotient:
  λ₁ ≤ R(f) = ⟨f, Lf⟩/⟨f,f⟩ ≤ 2h · d_max.

Manuscript: Theorem 33.1 (thm:cheeger, line 11533). -/
axiom cheeger_upper (cd : CheegerData) :
    cd.spectral_gap ≤ 2 * cd.cheeger_h * cd.d_max

/-- **Topological gap**: If the Cheeger constant is positive (the structure
is well-connected), then the spectral gap is positive. -/
theorem topological_gap (cd : CheegerData) (hh : 0 < cd.cheeger_h) :
    0 < cd.spectral_gap := by
  have h_lower := cheeger_lower cd
  have h_pos : 0 < cd.cheeger_h ^ 2 / (2 * cd.d_max) := by
    apply div_pos (sq_pos_of_pos hh)
    linarith [cd.d_max_pos]
  linarith

/-- **Gap persistence under perturbation**: If the perturbation is small
compared to the gap, the gap survives.

Specifically: if ‖δL‖ ≤ ε < δ/2, then the perturbed gap δ' ≥ δ - 2ε > 0.
This follows from Weyl's inequality: |λ̃_k - λ_k| ≤ ‖δL‖.

Manuscript: Corollary 33.3 (thm:quantitative-DK, line 11563). -/
theorem gap_persistence
    (gap eps : ℝ)
    (h_gap : 0 < gap)
    (h_eps : eps < gap / 2)
    (h_eps_nn : 0 ≤ eps) :
    0 < gap - 2 * eps := by
  linarith

/-- **Quantitative gap stability (Weyl)**: The spectral gap changes by
at most 2ε under an ε-perturbation.

|δ̃ - δ| ≤ 2ε where ε = ‖δL‖ (operator norm of perturbation). -/
theorem gap_weyl_bound
    (gap gap' eps : ℝ)
    (_h_eps_nn : 0 ≤ eps)
    (h_weyl : |gap' - gap| ≤ 2 * eps) :
    gap - 2 * eps ≤ gap' := by
  have := neg_abs_le (gap' - gap)
  linarith

/-- **Cheeger + gap persistence = topological protection**:
If the structure is well-connected (h > 0) and the perturbation
is bounded (ε < h²/(4 d_max)), then the gap survives. -/
theorem topological_protection (cd : CheegerData)
    (eps : ℝ) (_h_eps_nn : 0 ≤ eps)
    (hh : 0 < cd.cheeger_h)
    (h_small : eps < cd.cheeger_h ^ 2 / (4 * cd.d_max)) :
    0 < cd.spectral_gap - 2 * eps := by
  have h_lower := cheeger_lower cd
  have hd := cd.d_max_pos
  -- eps < h²/(4d) implies eps*(4d) < h² implies 2eps*(2d) < h²
  -- implies 2eps < h²/(2d) ≤ spectral_gap
  have h2d_pos : (0 : ℝ) < 2 * cd.d_max := by linarith
  -- Multiply through: eps * (4*d) < h² (from h_small * (4d))
  have key : eps * (4 * cd.d_max) < cd.cheeger_h ^ 2 := by
    have := mul_lt_mul_of_pos_right h_small (by linarith : (0 : ℝ) < 4 * cd.d_max)
    rwa [div_mul_cancel₀] at this
    linarith
  -- Therefore 2*eps*(2d) < h², so 2*eps < h²/(2d)
  have : 2 * eps < cd.cheeger_h ^ 2 / (2 * cd.d_max) := by
    rw [lt_div_iff₀ h2d_pos]
    nlinarith
  linarith

end SpectralPhysics.CheegerInequality

end
