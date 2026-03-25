/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Algebra.Hurwitz
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The Doubling Map: B ⊕ B·j → CayleyDickson B

Infrastructure for the Hurwitz theorem: given a composition subalgebra B
inside a composition algebra A, and an orthogonal unit j ⊥ B, we construct
the identification of B ⊕ B·j with CayleyDickson B.

## What this file proves

1. `orthogonal_image`: B·j ⊥ B
2. `right_mul_injective`: x ↦ x·j is injective
3. `norm_sq_decomp`: ‖a + bj‖² = ‖a‖² + ‖b‖²
4. `dim_doubling`: 2·dim(B) ≤ dim(A)

## References

* Ben-Shalom, "Spectral Physics", Theorem 22.5
* Baez, "The Octonions" (2002), Section 2
-/

noncomputable section

open scoped InnerProductSpace

variable {A : Type*} [NormedRing A] [InnerProductSpace ℝ A] [CompositionAlgebra A]

namespace SpectralPhysics.DoublingMap

/-! ### Part 1: Orthogonality of B and B·j -/

/-- **B·j ⊥ B**: For a composition subalgebra B and orthogonal unit j ⊥ B,
the image B·j is orthogonal to B. Uses double_polarization with a=1. -/
theorem orthogonal_image
    {B : Submodule ℝ A}
    (hB_mul : ∀ x y : A, x ∈ B → y ∈ B → x * y ∈ B)
    (hB_one : (1 : A) ∈ B)
    (j : A) (hj_perp_B : ∀ b : A, b ∈ B → @inner ℝ A _ j b = 0) :
    ∀ b₁ b₂ : A, b₁ ∈ B → b₂ ∈ B →
      @inner ℝ A _ b₁ (b₂ * j) = 0 := by
  intro b₁ b₂ hb₁ hb₂
  -- double_polarization(1, b₂, b₁, j):
  -- ⟨b₁, b₂*j⟩ + ⟨j, b₂*b₁⟩ = 2⟨1, b₂⟩⟨b₁, j⟩
  have h := CompositionAlgebra.double_polarization (1 : A) b₂ b₁ j
  simp only [one_mul] at h
  have h1 : @inner ℝ A _ j (b₂ * b₁) = 0 := hj_perp_B _ (hB_mul b₂ b₁ hb₂ hb₁)
  have h2 : @inner ℝ A _ b₁ j = 0 := by rw [real_inner_comm]; exact hj_perp_B b₁ hb₁
  -- h: ⟨b₁, b₂*j⟩ + ⟨j, b₂*b₁⟩ = 2*⟨1,b₂⟩*⟨b₁,j⟩
  -- Substituting h1=0, h2=0: ⟨b₁, b₂*j⟩ = 0
  have key : @inner ℝ A _ b₁ (b₂ * j) =
      2 * @inner ℝ A _ (1 : A) b₂ * @inner ℝ A _ b₁ j -
      @inner ℝ A _ j (b₂ * b₁) := by linarith
  rw [key, h1, h2, mul_zero, sub_zero]

/-! ### Part 2: Injectivity and dimension doubling -/

/-- Right multiplication by a unit element is injective. -/
theorem right_mul_injective (j : A) (hj : ‖j‖ = 1) :
    Function.Injective (fun x : A => x * j) := by
  intro a b hab
  have h1 : ‖a - b‖ = 0 := by
    have h2 : ‖a * j - b * j‖ = ‖a - b‖ := by
      rw [← sub_mul, CompositionAlgebra.norm_mul, hj, mul_one]
    simp [← h2, hab]
  exact sub_eq_zero.mp (norm_eq_zero.mp h1)

/-- Inner product version of right-mul orthogonality for the B⊥ map.
If b ∈ B and j ⊥ B, then b*j ∈ B⊥ (as a Submodule element). -/
theorem right_mul_mem_orthogonal
    {B : Submodule ℝ A}
    (hB_mul : ∀ x y : A, x ∈ B → y ∈ B → x * y ∈ B)
    (hB_one : (1 : A) ∈ B)
    (j : A) (hj_perp_B : ∀ b : A, b ∈ B → @inner ℝ A _ j b = 0)
    (b : A) (hb : b ∈ B) :
    b * j ∈ Bᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  exact (real_inner_comm u (b * j)).symm ▸
    orthogonal_image hB_mul hB_one j hj_perp_B u b hu hb

/-- **Dimension doubling**: 2·dim(B) ≤ dim(A).

Proof: R_j maps B injectively into B⊥ (orthogonal_image + right_mul_injective),
so dim(B) ≤ dim(B⊥). Combined with dim(B) + dim(B⊥) = dim(A). -/
theorem dim_doubling
    [FiniteDimensional ℝ A]
    {B : Submodule ℝ A}
    (hB_mul : ∀ x y : A, x ∈ B → y ∈ B → x * y ∈ B)
    (hB_one : (1 : A) ∈ B)
    (j : A) (hj_perp_B : ∀ b : A, b ∈ B → @inner ℝ A _ j b = 0)
    (hj_norm : ‖j‖ = 1)
    (h_smul_mul : ∀ (r : ℝ) (x : A), (r • x) * j = r • (x * j)) :
    2 * Module.finrank ℝ B ≤ Module.finrank ℝ A := by
  have h_orth := Submodule.finrank_add_finrank_orthogonal B
  suffices h : Module.finrank ℝ B ≤ Module.finrank ℝ Bᗮ by omega
  -- Construct an injective linear map from B to B⊥ via R_j
  -- R_j(b) = b * j, and b * j ∈ B⊥ by right_mul_mem_orthogonal.
  -- The map is injective by right_mul_injective.
  let φ : B →ₗ[ℝ] Bᗮ := {
    toFun := fun ⟨b, hb⟩ => ⟨b * j, right_mul_mem_orthogonal hB_mul hB_one j hj_perp_B b hb⟩
    map_add' := fun ⟨x, _⟩ ⟨y, _⟩ => by
      ext; simp [add_mul]
    map_smul' := fun r ⟨x, _⟩ => by
      ext; simp [mul_comm]
      exact h_smul_mul r x
  }
  have h_inj : Function.Injective φ := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ h
    have h_eq : a * j = b * j := by
      have := congr_arg Subtype.val h
      exact this
    exact Subtype.ext (right_mul_injective j hj_norm h_eq)
  exact LinearMap.finrank_le_finrank_of_injective h_inj

/-- **Norm decomposition**: ‖a + bj‖² = ‖a‖² + ‖b‖² when a ∈ B, b ∈ B, j ⊥ B. -/
theorem norm_sq_decomp
    {B : Submodule ℝ A}
    (hB_mul : ∀ x y : A, x ∈ B → y ∈ B → x * y ∈ B)
    (hB_one : (1 : A) ∈ B)
    (a b : A) (ha : a ∈ B) (hb : b ∈ B)
    (j : A) (hj_perp_B : ∀ c : A, c ∈ B → @inner ℝ A _ j c = 0)
    (hj_norm : ‖j‖ = 1) :
    ‖a + b * j‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [norm_add_sq_real]
  have h_orth : @inner ℝ A _ a (b * j) = 0 :=
    orthogonal_image hB_mul hB_one j hj_perp_B a b ha hb
  rw [h_orth, mul_zero, add_zero, CompositionAlgebra.norm_mul, hj_norm, mul_one]

end SpectralPhysics.DoublingMap

end
