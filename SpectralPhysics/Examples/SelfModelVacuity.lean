/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Axioms.SelfRefClosure
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases

/-!
# Examples/SelfModelVacuity.lean — vacuity tests for the two-piece self-model map

`RIGOROUS_WORKFLOW.md` requires that a predicate be shown neither trivially true
nor trivially false. For Axiom 3 in its 2026-09-06 form this file proves:

(i)  **Faithfulness HOLDS on a concrete structure.** The manuscript's own example,
     the unweighted triangle `K₃` (μ ≡ 1), has Laplacian matrix
     `[[2,-1,-1],[-1,2,-1],[-1,-1,2]]`, spectrum `{0, 3, 3}` (as a multiset, T1:
     `triangle_spectrum`), and `SpectrallyFaithful {triangle}` with the
     reconstruction returning the triangle (`triangle_reconstruct`).

(ii) **The one-piece predicate FAILS while the two-piece map separates.**
     A Laplacian-cospectral, NON-isomorphic pair of relational structures on
     `Fin 3` with μ ≡ 1:
       * `wTriangle`: weights k(0,1) = 1, k(0,2) = 1, k(1,2) = 4 (three edges),
       * `path`:      weights k(0,1) = 3, k(1,2) = 3, k(0,2) = 0 (two edges).
     Both Laplacians have characteristic polynomial `X³ − 12X² + 27X`, i.e.
     spectrum `{0, 3, 9}` (`wTriangle_path_cospectral`, T1: mathlib's
     `eigenvalues_eq_eigenvalues_iff` reduces this to a charpoly identity), the
     matrices differ (`wTriangle_ne_path`), so `¬ ZetaFaithful {wTriangle, path}`
     (`not_zetaFaithful_pair`) while `selfModel wTriangle ≠ selfModel path` and
     already the relative spectra differ (`pair_relSpec_ne`).

## Honest scope

* The pair in (ii) is a WEIGHTED cospectral pair (3 vertices). The smallest
  unweighted Laplacian-cospectral non-isomorphic pair lives on 6 vertices; its
  charpoly identity would need a symbolic 6×6 determinant in Lean and was not
  attempted. Weighted kernels are exactly Axiom 1's objects, so the pair is a
  genuine instance of the manuscript's class, and non-isomorphism is visible
  from the edge count (3 vs 2) — it is not a relabelling.
* (ii) shows separation via reconstruction (`R ∘ M = id`), not by computing the
  eigenprojections of the two structures explicitly.
* Nothing here concerns infinite dimensions or naturality (clause (ii)).
-/

open Matrix Polynomial SelfModelMap

noncomputable section

namespace SelfModelVacuity

-- ============================================================================
-- SECTION 1: CLASSICAL UNIT-MEASURE STRUCTURES ON Fin 3
-- ============================================================================

/-- Classical relational structure on `Fin 3` with unit measure and symmetric
real weights `w`. -/
def unitStructure (w : Matrix (Fin 3) (Fin 3) ℝ) (hw : ∀ x y, w x y = w y x) :
    RelationalStructure where
  X := Fin 3
  μ := fun _ => 1
  μ_pos := fun _ => one_pos
  k := fun x y => (w x y : ℂ)
  k_hermitian := by intro x y; simp [hw x y]

theorem unitStructure_classical (w : Matrix (Fin 3) (Fin 3) ℝ) (hw : ∀ x y, w x y = w y x)
    (hnn : ∀ x y, 0 ≤ w x y) : (unitStructure w hw).isClassical := by
  intro x y; simp [unitStructure, hnn x y]

/-- For unit measure and non-negative real weights the Laplacian matrix is the
weighted graph Laplacian `D − W`. -/
theorem unitStructure_laplacianMatrix (w : Matrix (Fin 3) (Fin 3) ℝ) (hw : ∀ x y, w x y = w y x)
    (hnn : ∀ x y, 0 ≤ w x y) (x y : Fin 3) :
    (unitStructure w hw).laplacianMatrix x y =
      (if x = y then ∑ z, (w x z : ℂ) else 0) - (w x y : ℂ) := by
  simp only [RelationalStructure.laplacianMatrix, RelationalStructure.weightFactor,
    RelationalStructure.phaseFactor.classical_eq_one _ (unitStructure_classical w hw hnn)]
  simp [unitStructure, Complex.norm_real, abs_of_nonneg (hnn _ _)]
  rfl

/-- The finite spectral triple of a unit-measure structure, typed over `Fin 3`. -/
def triple (w : Matrix (Fin 3) (Fin 3) ℝ) (hw : ∀ x y, w x y = w y x) :
    FiniteTriple (Fin 3) :=
  (unitStructure w hw).toFiniteTriple

-- Weight matrices -----------------------------------------------------------

/-- Unweighted triangle `K₃`. -/
def wTri : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 1; 1, 0, 1; 1, 1, 0]
/-- Weighted triangle: k(0,1) = 1, k(0,2) = 1, k(1,2) = 4. -/
def wWtri : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 1; 1, 0, 4; 1, 4, 0]
/-- Weighted path 0 — 1 — 2 with both weights 3. -/
def wPath : Matrix (Fin 3) (Fin 3) ℝ := !![0, 3, 0; 3, 0, 3; 0, 3, 0]

theorem wTri_symm : ∀ x y, wTri x y = wTri y x := by
  intro x y; fin_cases x <;> fin_cases y <;> rfl
theorem wWtri_symm : ∀ x y, wWtri x y = wWtri y x := by
  intro x y; fin_cases x <;> fin_cases y <;> rfl
theorem wPath_symm : ∀ x y, wPath x y = wPath y x := by
  intro x y; fin_cases x <;> fin_cases y <;> rfl
theorem wTri_nonneg : ∀ x y, 0 ≤ wTri x y := by
  intro x y; fin_cases x <;> fin_cases y <;> norm_num [wTri]
theorem wWtri_nonneg : ∀ x y, 0 ≤ wWtri x y := by
  intro x y; fin_cases x <;> fin_cases y <;> norm_num [wWtri]
theorem wPath_nonneg : ∀ x y, 0 ≤ wPath x y := by
  intro x y; fin_cases x <;> fin_cases y <;> norm_num [wPath]

/-- The manuscript's triangle. -/
def triangle : RelationalStructure := unitStructure wTri wTri_symm
/-- The weighted triangle of the cospectral pair. -/
def wTriangle : RelationalStructure := unitStructure wWtri wWtri_symm
/-- The weighted path of the cospectral pair. -/
def path : RelationalStructure := unitStructure wPath wPath_symm

-- Explicit Laplacian matrices ----------------------------------------------

def triL : Matrix (Fin 3) (Fin 3) ℂ := !![2, -1, -1; -1, 2, -1; -1, -1, 2]
def wtriL : Matrix (Fin 3) (Fin 3) ℂ := !![2, -1, -1; -1, 5, -4; -1, -4, 5]
def pathL : Matrix (Fin 3) (Fin 3) ℂ := !![3, -3, 0; -3, 6, -3; 0, -3, 3]

theorem triangle_laplacianMatrix : triangle.laplacianMatrix = triL := by
  have key : ∀ x y : Fin 3, triangle.laplacianMatrix x y = triL x y := by
    intro x y
    unfold triangle
    rw [unitStructure_laplacianMatrix wTri wTri_symm wTri_nonneg]
    fin_cases x <;> fin_cases y <;> simp [wTri, triL, Fin.sum_univ_three]
    all_goals norm_num
  exact Matrix.ext key

theorem wTriangle_laplacianMatrix : wTriangle.laplacianMatrix = wtriL := by
  have key : ∀ x y : Fin 3, wTriangle.laplacianMatrix x y = wtriL x y := by
    intro x y
    unfold wTriangle
    rw [unitStructure_laplacianMatrix wWtri wWtri_symm wWtri_nonneg]
    fin_cases x <;> fin_cases y <;> simp [wWtri, wtriL, Fin.sum_univ_three]
    all_goals norm_num
  exact Matrix.ext key

theorem path_laplacianMatrix : path.laplacianMatrix = pathL := by
  have key : ∀ x y : Fin 3, path.laplacianMatrix x y = pathL x y := by
    intro x y
    unfold path
    rw [unitStructure_laplacianMatrix wPath wPath_symm wPath_nonneg]
    fin_cases x <;> fin_cases y <;> simp [wPath, pathL, Fin.sum_univ_three]
    all_goals norm_num
  exact Matrix.ext key

-- ============================================================================
-- SECTION 2: VACUITY TEST (i) — FAITHFULNESS HOLDS ON THE TRIANGLE
-- ============================================================================

/-- The triangle as a finite triple over `Fin 3`. -/
def triangleTriple : FiniteTriple (Fin 3) := triple wTri wTri_symm

theorem triL_charpoly : triL.charpoly = X * (X - 3) ^ 2 := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp [triL, map_ofNat]
  ring

theorem triL_roots : triL.charpoly.roots = {0, 3, 3} := by
  have h3 : (X - 3 : ℂ[X]) = X - C 3 := by simp [map_ofNat]
  rw [triL_charpoly, roots_mul, roots_X, roots_pow, h3, roots_X_sub_C]
  · rfl
  · rw [h3]; exact mul_ne_zero X_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero 3))

/-- [T1] Piece one of the triangle's self-model is the multiset `{0, 3, 3}`
(the manuscript's spectrum for `K₃`). -/
theorem triangle_spectrum :
    Multiset.map (zetaPiece triangleTriple) Finset.univ.val = {0, 3, 3} := by
  apply Multiset.map_injective Complex.ofReal_injective
  rw [Multiset.map_map]
  have h := triangleTriple.2.roots_charpoly_eq_eigenvalues
  have hc : triangleTriple.1.charpoly = triL.charpoly := by
    show triangle.laplacianMatrix.charpoly = _
    rw [triangle_laplacianMatrix]
    rfl
  rw [hc, triL_roots] at h
  have h2 : Multiset.map Complex.ofReal ({0, 3, 3} : Multiset ℝ) = {0, 3, 3} := by simp
  rw [h2, h]
  rfl

/-- [T1] Vacuity test (i): the two-piece faithfulness predicate HOLDS on `{triangle}`. -/
theorem triangle_spectrallyFaithful : SpectrallyFaithful {triangleTriple} :=
  spectrallyFaithful _

/-- [T1] …and the reconstruction actually returns the triangle's Laplacian. -/
theorem triangle_reconstruct : reconstruct (selfModel triangleTriple) = triL := by
  rw [reconstruct_selfModel]
  exact triangle_laplacianMatrix

-- ============================================================================
-- SECTION 3: VACUITY TEST (ii) — ONE-PIECE FAILS, TWO-PIECE SEPARATES
-- ============================================================================

/-- The weighted triangle as a finite triple. -/
def wTriangleTriple : FiniteTriple (Fin 3) := triple wWtri wWtri_symm
/-- The weighted path as a finite triple. -/
def pathTriple : FiniteTriple (Fin 3) := triple wPath wPath_symm

/-- Both Laplacians have characteristic polynomial `X³ − 12X² + 27X`. -/
theorem wtriL_pathL_charpoly : wtriL.charpoly = pathL.charpoly := by
  rw [Matrix.charpoly, Matrix.charpoly, Matrix.det_fin_three, Matrix.det_fin_three]
  simp [wtriL, pathL, map_ofNat]
  ring

/-- [T1] The pair is Laplacian-cospectral: equal first pieces. -/
theorem wTriangle_path_cospectral : zetaPiece wTriangleTriple = zetaPiece pathTriple := by
  apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).mpr
  show wTriangle.laplacianMatrix.charpoly = path.laplacianMatrix.charpoly
  rw [wTriangle_laplacianMatrix, path_laplacianMatrix]
  exact wtriL_pathL_charpoly

/-- The pair consists of distinct triples (entry (0,2): −1 vs 0). -/
theorem wTriangle_ne_path : wTriangleTriple ≠ pathTriple := by
  intro h
  have h1 : wTriangle.laplacianMatrix = path.laplacianMatrix := congrArg Subtype.val h
  rw [wTriangle_laplacianMatrix, path_laplacianMatrix] at h1
  have := congrFun (congrFun h1 0) 2
  simp [wtriL, pathL] at this

/-- [T1] Vacuity test (ii): the ONE-PIECE predicate FAILS on the cospectral pair. -/
theorem not_zetaFaithful_pair : ¬ ZetaFaithful {wTriangleTriple, pathTriple} :=
  not_zetaFaithful_of_cospectral wTriangle_ne_path wTriangle_path_cospectral

/-- [T1] …while the two-piece predicate holds there. -/
theorem pair_spectrallyFaithful : SpectrallyFaithful {wTriangleTriple, pathTriple} :=
  spectrallyFaithful _

/-- [T1] The two-piece map separates the pair. -/
theorem pair_selfModel_ne : selfModel wTriangleTriple ≠ selfModel pathTriple :=
  fun h => wTriangle_ne_path (selfModel_injective h)

/-- [T1] The separation is carried by the SECOND piece (the first pieces coincide). -/
theorem pair_relSpec_ne :
    (selfModel wTriangleTriple).relSpec ≠ (selfModel pathTriple).relSpec :=
  relSpec_ne_of_cospectral wTriangle_ne_path wTriangle_path_cospectral

end SelfModelVacuity

end

-- Axiom audit (RIGOROUS_WORKFLOW.md): kernel axioms only, no sorryAx.
#print axioms SelfModelVacuity.triangle_spectrum
#print axioms SelfModelVacuity.triangle_spectrallyFaithful
#print axioms SelfModelVacuity.triangle_reconstruct
#print axioms SelfModelVacuity.wTriangle_path_cospectral
#print axioms SelfModelVacuity.not_zetaFaithful_pair
#print axioms SelfModelVacuity.pair_spectrallyFaithful
#print axioms SelfModelVacuity.pair_selfModel_ne
#print axioms SelfModelVacuity.pair_relSpec_ne
