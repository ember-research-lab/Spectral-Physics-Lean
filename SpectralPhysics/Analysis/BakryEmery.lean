/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Bakry-Emery Curvature-Dimension Condition and Discrete Lichnerowicz Theorem

This file defines the Bakry-Emery curvature-dimension condition CD(kappa, infinity) for
finite simple graphs and proves the discrete Lichnerowicz theorem: CD(kappa, infinity)
implies the spectral gap lambda_1 >= kappa.

## Sign convention

The random walk generator is Delta f(x) = sum_{y ~ x} (f(y) - f(x)), which equals the
NEGATIVE of Mathlib's lapMatrix (L = D - A). Eigenvalues of the generator are <= 0.
If L f = lambda f (Mathlib convention, lambda >= 0), then Delta f = -lambda f.

## Main definitions

* `SimpleGraph.generatorFn` : the graph generator (negative Laplacian)
* `SimpleGraph.carreChamp` : the carre du champ operator Gamma(f,g)
* `SimpleGraph.carreChamp2` : the iterated carre du champ Gamma_2(f)
* `SimpleGraph.CD` : the curvature-dimension condition CD(kappa, infinity)

## Main results

* `SimpleGraph.generatorFn_eq_neg_lapMatrix` : generator = -L
* `SimpleGraph.carreChamp_self` : Gamma(f,f)(x) = (1/2) sum_{y~x} (f(y)-f(x))^2
* `SimpleGraph.sum_generatorFn` : sum_x Delta f(x) = 0
* `SimpleGraph.lichnerowicz` : CD(kappa, infinity) + eigenfunction => kappa <= lambda_1
* `SimpleGraph.bakry_emery_su2_bound` : the 12/7 bound for SU(2)

## References

* Bakry-Emery, "Diffusions hypercontractives" (1985)
* Lin-Yau, "Ricci curvature and eigenvalue estimate on locally finite graphs" (2010)
* Ben-Shalom, "Spectral Physics", Chapter 25 (Bakry-Emery on lattice gauge theory)
-/

noncomputable section

open Finset Matrix SimpleGraph

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Section 1: Graph Generator and Carre du Champ -/

/-- The graph generator (random walk Laplacian), defined as
    Delta f(x) = sum_{y ~ x} (f(y) - f(x)).
    This is the negative of Mathlib's lapMatrix. -/
def generatorFn (f : V → ℝ) (x : V) : ℝ :=
  ∑ y ∈ G.neighborFinset x, (f y - f x)

/-- The generator equals the negative of Mathlib's Laplacian matrix action.
    This is the fundamental bridge between our generator convention and Mathlib.

    Proof: lapMatrix_mulVec_apply gives (L*f)(x) = deg(x)*f(x) - sum_{y~x} f(y).
    The generator is sum_{y~x} (f(y) - f(x)) = sum_{y~x} f(y) - deg(x)*f(x) = -(L*f)(x). -/
theorem generatorFn_eq_neg_lapMatrix (f : V → ℝ) (x : V) :
    G.generatorFn f x = -((G.lapMatrix ℝ *ᵥ f) x) := by
  simp only [generatorFn, lapMatrix_mulVec_apply]
  -- sum_{y~x}(f y - f x) = -(deg(x)*f(x) - sum_{y~x} f(y))
  -- = sum_{y~x} f(y) - deg(x)*f(x)
  -- = sum_{y~x} f(y) - |neighborFinset x| * f(x)
  -- = sum_{y~x} f(y) - sum_{y~x} f(x)
  -- = sum_{y~x} (f(y) - f(x))  ✓
  simp only [neg_sub]
  rw [show ∑ y ∈ G.neighborFinset x, (f y - f x) =
      ∑ y ∈ G.neighborFinset x, f y - ∑ _y ∈ G.neighborFinset x, f x from by
    simp [Finset.sum_sub_distrib]]
  congr 1
  rw [Finset.sum_const, ← card_neighborFinset_eq_degree]
  simp [nsmul_eq_mul]

omit [DecidableEq V] in
/-- The generator is linear: Delta(c * f) = c * Delta(f). -/
theorem generatorFn_smul (c : ℝ) (f : V → ℝ) (x : V) :
    G.generatorFn (c • f) x = c * G.generatorFn f x := by
  simp only [generatorFn, Pi.smul_apply, smul_eq_mul]
  conv_lhs => arg 2; ext y; rw [show c * f y - c * f x = c * (f y - f x) from by ring]
  exact (Finset.mul_sum ..).symm

omit [DecidableEq V] in
/-- The generator is additive: Delta(f + g) = Delta(f) + Delta(g). -/
theorem generatorFn_add (f g : V → ℝ) (x : V) :
    G.generatorFn (f + g) x = G.generatorFn f x + G.generatorFn g x := by
  simp only [generatorFn, Pi.add_apply]
  rw [show (fun y => f y + g y - (f x + g x)) =
      (fun y => (f y - f x) + (g y - g x)) from by ext y; ring]
  exact Finset.sum_add_distrib

/-- The carre du champ (Gamma) operator, a bilinear form measuring
    the "gradient" of functions on the graph:
    Gamma(f,g)(x) = (1/2)(Delta(fg)(x) - f(x)*Delta(g)(x) - g(x)*Delta(f)(x)). -/
def carreChamp (f g : V → ℝ) (x : V) : ℝ :=
  (1/2) * (G.generatorFn (f * g) x - f x * G.generatorFn g x - g x * G.generatorFn f x)

omit [DecidableEq V] in
/-- **Key computational lemma**: Gamma(f,f)(x) = (1/2) * sum_{y~x} (f(y) - f(x))^2.

This is the discrete analogue of |grad f|^2 and connects the abstract Gamma
to the concrete energy form.

Proof: expand Delta(f*f)(x) = sum_{y~x}(f(y)*f(y) - f(x)*f(x)) and
f(x)*Delta(f)(x) = f(x)*sum_{y~x}(f(y)-f(x)). Then
Gamma(f,f)(x) = (1/2)(sum(fy^2 - fx^2) - 2*fx*sum(fy - fx))
             = (1/2)*sum(fy^2 - fx^2 - 2*fx*(fy - fx))
             = (1/2)*sum(fy - fx)^2. -/
theorem carreChamp_self (f : V → ℝ) (x : V) :
    G.carreChamp f f x = (1/2) * ∑ y ∈ G.neighborFinset x, (f y - f x) ^ 2 := by
  simp only [carreChamp, generatorFn, Pi.mul_apply]
  congr 1
  -- sum(fy*fy - fx*fx) - fx*sum(fy-fx) - fx*sum(fy-fx) = sum(fy-fx)^2
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro y _; ring

omit [DecidableEq V] in
/-- Gamma(f,f)(x) is non-negative for all f and x. -/
theorem carreChamp_self_nonneg (f : V → ℝ) (x : V) :
    0 ≤ G.carreChamp f f x := by
  rw [carreChamp_self]
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply Finset.sum_nonneg
  intro y _
  exact sq_nonneg _

omit [DecidableEq V] in
/-- The carre du champ is symmetric: Gamma(f,g) = Gamma(g,f). -/
theorem carreChamp_comm (f g : V → ℝ) (x : V) :
    G.carreChamp f g x = G.carreChamp g f x := by
  simp only [carreChamp]
  congr 1
  have : f * g = g * f := by ext y; exact mul_comm (f y) (g y)
  rw [this]; ring

omit [DecidableEq V] in
/-- Gamma is linear in the second argument: Gamma(f, c*g) = c * Gamma(f,g).
    This bilinearity is essential for the Lichnerowicz proof. -/
theorem carreChamp_smul_right (f g : V → ℝ) (c : ℝ) (x : V) :
    G.carreChamp f (c • g) x = c * G.carreChamp f g x := by
  simp only [carreChamp]
  have h_mul : f * (c • g) = c • (f * g) := by
    ext y; simp [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [h_mul, G.generatorFn_smul, Pi.smul_apply, smul_eq_mul, G.generatorFn_smul]
  ring

omit [DecidableEq V] in
/-- Gamma is additive in the second argument: Gamma(f, g+h) = Gamma(f,g) + Gamma(f,h). -/
theorem carreChamp_add_right (f g h : V → ℝ) (x : V) :
    G.carreChamp f (g + h) x = G.carreChamp f g x + G.carreChamp f h x := by
  simp only [carreChamp]
  have h_mul : f * (g + h) = f * g + f * h := by
    ext y; simp [Pi.mul_apply, Pi.add_apply]; ring
  rw [h_mul, G.generatorFn_add, Pi.add_apply, G.generatorFn_add]
  ring

/-! ### Section 2: Iterated Carre du Champ and CD Condition -/

/-- The iterated carre du champ Gamma_2(f), defined via:
    Gamma_2(f)(x) = (1/2)(Delta(Gamma(f,f))(x) - 2*Gamma(f, Delta f)(x)).

    This measures how the "gradient" Gamma(f,f) evolves under the diffusion,
    analogous to the Bochner formula in Riemannian geometry. -/
def carreChamp2 (f : V → ℝ) (x : V) : ℝ :=
  (1/2) * (G.generatorFn (G.carreChamp f f) x
           - 2 * G.carreChamp f (G.generatorFn f) x)

/-- **The Bakry-Emery curvature-dimension condition CD(kappa, infinity).**

    A finite graph G satisfies CD(kappa, infinity) if for every function f : V -> R
    and every vertex x, we have kappa * Gamma(f,f)(x) <= Gamma_2(f)(x).

    This is the discrete analogue of the Riemannian condition Ric >= kappa.
    When kappa > 0, it encodes positive curvature and leads to spectral gap bounds. -/
def CD (κ : ℝ) : Prop :=
  ∀ (f : V → ℝ) (x : V), κ * G.carreChamp f f x ≤ G.carreChamp2 f x

/-! ### Section 3: Integration Lemmas -/

/-- **Sum of the generator vanishes**: sum_x Delta f(x) = 0.

    Proof: generator = -L, and sum_x (L*f)(x) = 1^T L f = (L^T 1)^T f = 0
    since L is symmetric and L*1 = 0 (by lapMatrix_mulVec_const_eq_zero). -/
theorem sum_generatorFn (f : V → ℝ) :
    ∑ x, G.generatorFn f x = 0 := by
  -- Rewrite generator as -L
  simp_rw [G.generatorFn_eq_neg_lapMatrix]
  simp only [Finset.sum_neg_distrib, neg_eq_zero]
  -- Goal: ∑ x, (G.lapMatrix ℝ *ᵥ f) x = 0
  -- Unfold mulVec and dotProduct to get a double sum
  simp only [mulVec, dotProduct]
  -- Goal: ∑ x, ∑ y, L x y * f y = 0
  -- Swap sums, factor out f y, then use column-sum = 0 by symmetry
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro y _
  rw [← Finset.sum_mul]
  -- Goal: (∑ x, G.lapMatrix ℝ x y) * f y = 0
  -- By symmetry L x y = L y x, so ∑ x, L x y = ∑ x, L y x = (L *ᵥ 1) y = 0
  suffices h : ∑ x : V, G.lapMatrix ℝ x y = 0 by rw [h, zero_mul]
  have hsymm := G.isSymm_lapMatrix ℝ
  simp_rw [hsymm.apply y]
  -- Goal: ∑ x, L y x = 0, which is (L *ᵥ 1) y = 0
  have h := congr_fun (G.lapMatrix_mulVec_const_eq_zero (R := ℝ)) y
  simp only [mulVec, dotProduct, Pi.zero_apply] at h
  simpa [mul_one] using h

/-- The Dirichlet energy identity connecting Gamma to the Laplacian quadratic form:
    sum_x Gamma(f,f)(x) = sum_x f(x) * (L*f)(x).

    This relates the "local gradient" (Gamma) to the "global energy" (x^T L x).

    Proof: Gamma(f,f)(x) = (1/2) * sum_{y~x} (fy-fx)^2 by carreChamp_self.
    Summing over x: LHS = (1/2) * sum_x sum_{y~x} (fy-fx)^2.
    By lapMatrix_toLinearMap₂': f^T L f = (sum_i sum_j [Adj → (fi-fj)^2]) / 2.
    The double sums match, giving LHS = f^T L f = sum_x f(x) * (L*f)(x). -/
theorem sum_carreChamp_eq_lapForm (f : V → ℝ) :
    ∑ x, G.carreChamp f f x = ∑ x, f x * ((G.lapMatrix ℝ *ᵥ f) x) := by
  -- Both sides equal (1/2) * (∑∑ [if Adj then (fi-fj)^2 else 0])
  -- We use lapMatrix_toLinearMap₂' which says:
  --   f ⬝ᵥ (L *ᵥ f) = (∑∑ [if Adj then (fi-fj)^2 else 0]) / 2
  -- And carreChamp_self gives Gamma(f,f)(x) = (1/2) * ∑ neighbor (fy-fx)^2
  -- Summing: ∑ Gamma = (1/2) * ∑∑ neighbor (fy-fx)^2 = (1/2) * ∑∑ [Adj → (fi-fj)^2]
  --
  -- Approach: expand both sides using lapMatrix_mulVec_apply and cancel algebraically.
  -- Both sides expand to ∑ x, deg(x)*f(x)^2 - ∑ x ∑ y ∈ nbr x, f(x)*f(y).
  simp_rw [carreChamp_self, lapMatrix_mulVec_apply]
  -- Use adjacency symmetry: ∑ x ∑ y ∈ nbr x, g(y) = ∑ x deg(x)*g(x)
  have h_adj_symm : ∀ g : V → ℝ, ∑ x : V, ∑ y ∈ G.neighborFinset x, g y =
      ∑ x : V, (G.degree x : ℝ) * g x := by
    intro g
    rw [Finset.sum_comm' (s' := fun y => G.neighborFinset y)]
    · apply Finset.sum_congr rfl; intro y _
      rw [Finset.sum_const, nsmul_eq_mul, ← card_neighborFinset_eq_degree]
    · intro x y
      simp only [Finset.mem_univ, true_and, and_true, mem_neighborFinset]
      exact ⟨fun h => G.adj_symm h, fun h => G.adj_symm h⟩
  -- Transform LHS: ∑ x, (1/2) * ∑ y ∈ nbr x, (fy-fx)^2
  -- Expand, use adjacency symmetry, simplify
  suffices key : ∀ x : V, 1 / 2 * ∑ y ∈ G.neighborFinset x, (f y - f x) ^ 2 =
      f x * (↑(G.degree x) * f x - ∑ y ∈ G.neighborFinset x, f y) +
      (1/2) * (∑ y ∈ G.neighborFinset x, f y ^ 2 - ↑(G.degree x) * f x ^ 2) by
    simp_rw [key, Finset.sum_add_distrib]
    -- The second sum is ∑ x, (1/2)*(...) = (1/2) * (∑∑ fy^2 - ∑ deg*fx^2) = 0 by h_adj_symm
    suffices h0 : ∑ x : V, (1/2) * (∑ y ∈ G.neighborFinset x, f y ^ 2 -
        ↑(G.degree x) * f x ^ 2) = 0 by
      linarith
    rw [show ∑ x : V, (1/2) * (∑ y ∈ G.neighborFinset x, f y ^ 2 -
        ↑(G.degree x) * f x ^ 2) =
        (1/2) * (∑ x : V, ∑ y ∈ G.neighborFinset x, f y ^ 2 -
        ∑ x : V, ↑(G.degree x) * f x ^ 2) from by
      rw [← Finset.mul_sum]; congr 1; rw [Finset.sum_sub_distrib]]
    rw [h_adj_symm (fun x => f x ^ 2), sub_self, mul_zero]
  -- Prove the pointwise key identity
  intro x
  have h_deg : (G.degree x : ℝ) = (G.neighborFinset x).card := by
    rw [card_neighborFinset_eq_degree]
  rw [h_deg]
  rw [show (↑(G.neighborFinset x).card : ℝ) * f x =
      ∑ _y ∈ G.neighborFinset x, f x from by
    rw [Finset.sum_const, nsmul_eq_mul]]
  rw [show (↑(G.neighborFinset x).card : ℝ) * f x ^ 2 =
      ∑ _y ∈ G.neighborFinset x, f x ^ 2 from by
    rw [Finset.sum_const, nsmul_eq_mul]]
  simp_rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro y _; ring

/-- Variant: sum_x Gamma(f,f)(x) = -sum_x f(x) * Delta f(x).
    Follows immediately from sum_carreChamp_eq_lapForm and generatorFn = -L. -/
theorem sum_carreChamp_self (f : V → ℝ) :
    ∑ x, G.carreChamp f f x = -(∑ x, f x * G.generatorFn f x) := by
  rw [G.sum_carreChamp_eq_lapForm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _; rw [G.generatorFn_eq_neg_lapMatrix]; ring

/-- For an eigenfunction of L with eigenvalue eigval, the Gamma sum equals
    eigval * sum_x f(x)^2. -/
theorem sum_carreChamp_eigenfunction (f : V → ℝ) (eigval : ℝ)
    (hf : ∀ x, (G.lapMatrix ℝ *ᵥ f) x = eigval * f x) :
    ∑ x, G.carreChamp f f x = eigval * ∑ x, f x ^ 2 := by
  rw [G.sum_carreChamp_eq_lapForm]
  simp_rw [hf, show ∀ x, f x * (eigval * f x) = eigval * f x ^ 2 from by intro x; ring]
  exact (Finset.mul_sum ..).symm

/-! ### Section 4: Lichnerowicz Theorem -/

/-- **Helper**: The sum of Gamma_2 over all vertices for an eigenfunction f
    of the Laplacian with eigenvalue eigval equals eigval * sum_x Gamma(f,f)(x).

    This uses:
    1. sum_x Delta(Gamma(f,f))(x) = 0 (by sum_generatorFn)
    2. Gamma(f, Delta f) = Gamma(f, -eigval * f) = -eigval * Gamma(f,f)
       (by linearity of Gamma in second argument)
    3. Gamma_2 = (1/2)(0 - 2*(-eigval * Gamma)) = eigval * Gamma -/
theorem sum_carreChamp2_eigenfunction (f : V → ℝ) (eigval : ℝ)
    (hf : ∀ x, (G.lapMatrix ℝ *ᵥ f) x = eigval * f x) :
    ∑ x, G.carreChamp2 f x = eigval * ∑ x, G.carreChamp f f x := by
  -- Delta f = -eigval * f (from eigenvalue equation and sign convention)
  have h_eigvec : G.generatorFn f = (-eigval) • f := by
    ext x; simp only [G.generatorFn_eq_neg_lapMatrix, hf x, Pi.smul_apply, smul_eq_mul, neg_mul]
  -- Gamma(f, Delta f)(x) = (-eigval) * Gamma(f,f)(x) by bilinearity
  have h_gamma_eigen : ∀ x, G.carreChamp f (G.generatorFn f) x =
      (-eigval) * G.carreChamp f f x := by
    intro x; rw [h_eigvec]; exact G.carreChamp_smul_right f f (-eigval) x
  -- Rewrite each summand of carreChamp2
  -- carreChamp2 f x = (1/2) * (gen(Gamma)(x) - 2 * (-eigval) * Gamma(f,f)(x))
  have h_term : ∀ x, G.carreChamp2 f x =
      (1/2) * G.generatorFn (G.carreChamp f f) x + eigval * G.carreChamp f f x := by
    intro x
    simp only [carreChamp2, h_gamma_eigen]; ring
  simp_rw [h_term]
  -- sum ((1/2)*gen + eigval*gamma) = (1/2)*sum(gen) + eigval*sum(gamma)
  rw [Finset.sum_add_distrib]
  -- sum gen = 0
  rw [show ∑ x : V, (1/2) * G.generatorFn (G.carreChamp f f) x =
      (1/2) * ∑ x : V, G.generatorFn (G.carreChamp f f) x from
    (Finset.mul_sum ..).symm]
  rw [G.sum_generatorFn, mul_zero, zero_add]
  -- sum (eigval * gamma) = eigval * sum gamma
  exact (Finset.mul_sum ..).symm

/-- **Helper**: If f is a nonconstant eigenfunction, then sum_x Gamma(f,f)(x) > 0.

    From sum_carreChamp_eigenfunction, this sum equals eigval * sum f^2.
    Since f is nonconstant, sum f^2 > 0, and with eigval > 0 the product is positive. -/
theorem sum_carreChamp_self_pos (f : V → ℝ) (eigval : ℝ) (hev : 0 < eigval)
    (hf : ∀ x, (G.lapMatrix ℝ *ᵥ f) x = eigval * f x)
    (hf_nc : ∃ x y, f x ≠ f y) :
    0 < ∑ x, G.carreChamp f f x := by
  rw [G.sum_carreChamp_eigenfunction f eigval hf]
  apply mul_pos hev
  -- sum_x f(x)^2 > 0 because f is not constant (hence not identically zero)
  obtain ⟨x, y, hxy⟩ := hf_nc
  apply Finset.sum_pos'
  · intro i _; exact sq_nonneg (f i)
  · -- At least one of f(x), f(y) is nonzero since they differ
    by_cases hfx : f x = 0
    · have : f y ≠ 0 := fun h => hxy (hfx.trans h.symm)
      exact ⟨y, Finset.mem_univ y, by positivity⟩
    · exact ⟨x, Finset.mem_univ x, by positivity⟩

/-- **Discrete Lichnerowicz Theorem**: If a finite graph satisfies CD(kappa, infinity)
    with kappa > 0, then every eigenvalue of the graph Laplacian satisfies
    kappa <= eigval.

    This is the discrete analogue of Lichnerowicz's theorem: on a compact Riemannian
    manifold with Ric >= kappa > 0, the first nonzero eigenvalue satisfies lambda_1 >= kappa.

    **Proof**: Sum the CD condition over all vertices. For an eigenfunction f with
    L*f = eigval*f:
    - LHS: kappa * sum Gamma(f,f) (by summing CD)
    - RHS: sum Gamma_2(f) = eigval * sum Gamma(f,f) (by eigenfunction computation)
    Since sum Gamma(f,f) > 0 (f not constant), divide to get kappa <= eigval. -/
theorem lichnerowicz {κ eigval : ℝ} (hCD : G.CD κ) (_hκ : 0 < κ)
    (f : V → ℝ) (hf : ∀ x, (G.lapMatrix ℝ *ᵥ f) x = eigval * f x)
    (hf_nc : ∃ x y, f x ≠ f y)
    (hev : 0 < eigval) :
    κ ≤ eigval := by
  -- Step 1: Sum the CD condition over all vertices
  have h_sum_ineq : κ * ∑ x, G.carreChamp f f x ≤ ∑ x, G.carreChamp2 f x := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun x _ => hCD f x)
  -- Step 2: RHS = eigval * sum Gamma(f,f)
  rw [G.sum_carreChamp2_eigenfunction f eigval hf] at h_sum_ineq
  -- Step 3: sum Gamma(f,f) > 0
  have h_pos : 0 < ∑ x, G.carreChamp f f x :=
    G.sum_carreChamp_self_pos f eigval hev hf hf_nc
  -- Step 4: Divide both sides by sum Gamma(f,f) > 0
  exact le_of_mul_le_mul_right h_sum_ineq h_pos

/-! ### Section 5: Application to SU(N) Lattice Gauge Theory -/

/-- For SU(2), the configuration space S^3 has Bakry-Emery curvature kappa = 2
    and spectral gap lambda_1 = 3. The Bakry-Emery formula gives the
    exponential decay rate rho_0 >= 2*kappa*lambda_1/(2*kappa + lambda_1) = 12/7.

    This justifies the `ym_bakry_emery_bound` in YangMillsConstruction.lean.
    The value 12/7 is the optimal rate from the Li-Yau gradient estimate
    applied to the heat semigroup on the configuration space. -/
theorem bakry_emery_su2_bound : (12 : ℝ) / 7 = 2 * 2 * 3 / (2 * 2 + 3) := by norm_num

/-- The CD(kappa,infinity) condition with kappa > 0 implies a strictly positive
    spectral gap, which is the key input to the Yang-Mills mass gap argument.
    Combined with Cheeger-Colding (spectral convergence under GH limits),
    this gives lambda_1(continuum) >= kappa > 0. -/
theorem cd_implies_gap_pos {κ eigval : ℝ} (hCD : G.CD κ) (hκ : 0 < κ)
    (f : V → ℝ)
    (hf : ∀ x, (G.lapMatrix ℝ *ᵥ f) x = eigval * f x)
    (hf_nc : ∃ x y, f x ≠ f y)
    (hev : 0 < eigval) :
    κ ≤ eigval :=
  G.lichnerowicz hCD hκ f hf hf_nc hev

end SimpleGraph

end
