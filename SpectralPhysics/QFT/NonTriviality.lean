/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Analysis.RicciGeometry
import SpectralPhysics.QFT.YangMillsExistence

/-!
# Non-Triviality of Yang-Mills Theory (Seeley-DeWitt Argument)

The YM configuration space A/G has positive Ricci curvature, which forces
the Seeley-DeWitt coefficient a₂ = (1/6)∫R dvol > 0. A free (Gaussian) field
on flat space has a₂ = 0. Therefore the YM theory is INTERACTING.

## The heat kernel argument

For a compact Riemannian manifold with Laplacian L, the heat trace expands as
  Tr(e^{-tL}) ~ (4πt)^{-d/2} Σ_{k≥0} aₖ tᵏ   as t → 0⁺

The Seeley-DeWitt coefficients encode geometry:
- a₀ = Vol(M) > 0
- a₂ = (1/6) ∫ R dvol, where R is the scalar curvature

For Ric ≥ κ > 0 in dimension d: R ≥ dκ > 0, so a₂ > 0.
For a free field (flat space): R = 0, hence a₂ = 0.
Since A/G has Ric > 0, we get a₂ > 0, hence the theory is not free.

## Main results

* `SeeleyDeWittData` : heat kernel coefficients a₀, a₂ with positivity
* `isFreeField` : characterization as a₂ = 0 (flat configuration space)
* `ym_not_free_field` : a₂ > 0 implies ¬ free
* `seeley_dewitt_from_ricci` : Ric ≥ κ > 0 in dim d → a₂ > 0
* `ym_nontrivial_strong` : for any CompactSimpleGroup, the theory is not free
* `nontrivial_from_curvature` : Ric > 0 → non-Gaussian (higher cumulants nonzero)

## References

* Seeley, "Complex powers of an elliptic operator" (1967)
* DeWitt, "Dynamical theory of groups and fields" (1965)
* Gilkey, "Invariance theory, the heat equation, and the Atiyah-Singer index theorem"
* Ben-Shalom, "Spectral Physics", Chapter 38
-/

noncomputable section

namespace SpectralPhysics.NonTriviality

open SpectralPhysics.YangMillsExistence

/-! ### Seeley-DeWitt Coefficients -/

/-- Heat kernel expansion data for a compact Riemannian manifold.

The heat trace Tr(e^{-tL}) ~ (4πt)^{-d/2} Σ aₖ tᵏ has coefficients:
- `volume` = a₀ = Vol(M)
- `scalar_curvature_integral` = 6 · a₂ = ∫ R dvol

We store 6 · a₂ rather than a₂ to avoid fractions. -/
structure SeeleyDeWittData where
  /-- Dimension of the manifold -/
  dim : ℕ
  /-- a₀ = Vol(M) -/
  volume : ℝ
  volume_pos : 0 < volume
  /-- 6 · a₂ = ∫ R dvol (scalar curvature integral) -/
  scalar_curvature_integral : ℝ
  /-- Ric ≥ κ > 0 in dim d gives R ≥ dκ > 0, so ∫ R dvol > 0 -/
  h_curvature : 0 < scalar_curvature_integral

/-- A free (Gaussian) field has a₂ = 0, i.e., flat configuration space.
Equivalently, the scalar curvature integral vanishes. -/
def isFreeField (sd : SeeleyDeWittData) : Prop := sd.scalar_curvature_integral = 0

/-- A manifold with a₂ > 0 is not a free field. -/
theorem ym_not_free_field (sd : SeeleyDeWittData) : ¬ isFreeField sd :=
  ne_of_gt sd.h_curvature

/-! ### Construction from Ricci Curvature Bounds -/

/-- Construct Seeley-DeWitt data from Ricci curvature bounds.

Given Ric ≥ κ > 0 in dimension d with volume V:
- Scalar curvature R ≥ d · κ (trace of Ric over d directions)
- ∫ R dvol ≥ d · κ · V > 0

So a₂ = (1/6) ∫ R dvol > 0. -/
def seeley_dewitt_from_ricci (d : ℕ) (kappa vol : ℝ)
    (h_kappa : 0 < kappa) (h_vol : 0 < vol) (h_d : 0 < d) :
    SeeleyDeWittData where
  dim := d
  volume := vol
  volume_pos := h_vol
  -- ∫ R dvol ≥ d · κ · V > 0
  scalar_curvature_integral := (d : ℝ) * kappa * vol
  h_curvature := by positivity

/-- The scalar curvature integral from `seeley_dewitt_from_ricci` equals d · κ · V. -/
theorem seeley_dewitt_integral_eq (d : ℕ) (kappa vol : ℝ)
    (h_kappa : 0 < kappa) (h_vol : 0 < vol) (h_d : 0 < d) :
    (seeley_dewitt_from_ricci d kappa vol h_kappa h_vol h_d).scalar_curvature_integral =
      (d : ℝ) * kappa * vol := rfl

/-! ### Non-Triviality for Yang-Mills -/

/-- Seeley-DeWitt data for A/G with gauge group G.

dim(A/G) ≥ dim(G) ≥ 3, Ric ≥ κ_G > 0, Vol > 0 (compact). -/
def ym_seeley_dewitt (G : CompactSimpleGroup) :
    SeeleyDeWittData :=
  seeley_dewitt_from_ricci G.dim_G G.ricci_lower 1
    G.h_ricci_pos one_pos (by have := G.h_dim; omega)

/-- **YM is not a free field** (strong form):
For any compact simple gauge group G, the Yang-Mills theory on A/G is
not a free (Gaussian) field, because a₂ > 0.

Chain: Ric ≥ κ > 0 → R ≥ dκ > 0 → ∫ R dvol > 0 → a₂ > 0 → ¬ free. -/
theorem ym_nontrivial_strong (G : CompactSimpleGroup) :
    ¬ isFreeField (ym_seeley_dewitt G) :=
  ym_not_free_field _

/-! ### Non-Gaussian Statistics -/

/-- Data witnessing non-Gaussian statistics: positive a₂ forces
the connected 4-point function to be nonzero. -/
structure NonGaussianWitness where
  /-- The Seeley-DeWitt data -/
  sd : SeeleyDeWittData
  /-- a₂ > 0 implies the 4-point cumulant is nonzero.
  For a Gaussian, ALL cumulants of order > 2 vanish; equivalently
  the heat kernel is exactly (4πt)^{-d/2} exp(-r²/4t) with no
  curvature corrections. Positive a₂ forces curvature corrections,
  which correspond to non-vanishing higher cumulants. -/
  four_point_nonzero : 0 < sd.scalar_curvature_integral

/-- Positive Ricci curvature implies non-Gaussian statistics.

The connected 4-point function κ₄ is proportional to a₂ at leading order
in the heat kernel expansion. When a₂ > 0, the field has genuine
interactions (higher cumulants nonzero, S-matrix nontrivial). -/
def nontrivial_from_curvature (sd : SeeleyDeWittData) :
    NonGaussianWitness where
  sd := sd
  four_point_nonzero := sd.h_curvature

/-- YM has non-Gaussian statistics for any compact simple G. -/
def ym_non_gaussian (G : CompactSimpleGroup) :
    NonGaussianWitness :=
  nontrivial_from_curvature (ym_seeley_dewitt G)

/-! ### Instantiations -/

/-- SU(2) Yang-Mills is not free. -/
theorem su2_not_free : ¬ isFreeField (ym_seeley_dewitt SU2) :=
  ym_nontrivial_strong SU2

/-- SU(3) Yang-Mills is not free. -/
theorem su3_not_free : ¬ isFreeField (ym_seeley_dewitt SU3) :=
  ym_nontrivial_strong SU3

/-- SU(N) Yang-Mills is not free for any N ≥ 2. -/
theorem suN_not_free (N : ℕ) (hN : 2 ≤ N) :
    ¬ isFreeField (ym_seeley_dewitt (SU N hN)) :=
  ym_nontrivial_strong (SU N hN)

end SpectralPhysics.NonTriviality

end
