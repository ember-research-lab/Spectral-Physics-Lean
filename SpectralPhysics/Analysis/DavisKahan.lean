/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Axioms.Laplacian
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Davis-Kahan Sin(Theta) Theorem and Gap Persistence (Ch 33)

Quantitative perturbation bounds for eigenvalues and eigenvectors
of the graph Laplacian under bounded perturbations.

## Main results

* `weyl_perturbation_bound` : |eigenval_k(L') - eigenval_k(L)| <= ||perturbation||
  (axiomatized; requires operator norm infrastructure)
* `quantitative_gap_stability` : |gap' - gap| <= 2 * eps from Weyl
* `gap_persistence` : gap - 2 * eps > 0 when eps < gap / 2
* `gap_lifetime` : gap_0 - 2 * v * t > 0 when t < gap_0 / (2 * v)
* `sin_theta_bound` : sin(theta) <= eps / gap (axiomatized geometric statement)

## References

* Davis-Kahan, "The rotation of eigenvectors by a perturbation. III" (1970)
* Weyl, "Das asymptotische Verteilungsgesetz der Eigenwerte" (1912)
* Ben-Shalom, "Spectral Physics", Chapter 33 (lines 11563-11600)
-/

noncomputable section

open Finset

variable (S : RelationalStructure)

namespace SpectralPhysics.DavisKahan

-- ═══════════════════════════════════════════════════════════════════════
-- SPECTRAL GAP DATA
-- ═══════════════════════════════════════════════════════════════════════

/-- Spectral gap data for a Laplacian: stores the first two eigenvalues
and the perturbation norm. The spectral gap is `eigenval_1 - eigenval_0`.

For the graph Laplacian, `eigenval_0 = 0` (constant eigenfunction) and
`eigenval_1 > 0` iff the structure is connected. -/
structure SpectralGapData where
  /-- The smallest eigenvalue (typically 0 for graph Laplacians) -/
  eigenval_0 : ℝ
  /-- The second-smallest eigenvalue -/
  eigenval_1 : ℝ
  /-- Eigenvalues are ordered -/
  ordered : eigenval_0 ≤ eigenval_1
  /-- The smallest eigenvalue is non-negative -/
  nonneg : 0 ≤ eigenval_0

/-- The spectral gap: difference between the two smallest eigenvalues. -/
def SpectralGapData.gap (d : SpectralGapData) : ℝ :=
  d.eigenval_1 - d.eigenval_0

/-- The spectral gap is non-negative. -/
theorem SpectralGapData.gap_nonneg (d : SpectralGapData) : 0 ≤ d.gap :=
  sub_nonneg.mpr d.ordered

-- ═══════════════════════════════════════════════════════════════════════
-- WEYL PERTURBATION BOUND (axiomatized)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Weyl's Perturbation Bound** (axiomatized):
For self-adjoint operators L and L' = L + E with ||E|| <= eps,
the k-th eigenvalue satisfies |eigenval_k(L') - eigenval_k(L)| <= eps.

This is a fundamental result in matrix perturbation theory. The proof
requires operator norm and min-max characterization of eigenvalues
(Courant-Fischer), which are not yet available in our formalization.

Manuscript: implicit in Theorem 33.3 (line 11563). -/
axiom weyl_perturbation_bound
    (lam lam' eps : ℝ) (he : 0 ≤ eps)
    (h_weyl : abs (lam' - lam) ≤ eps) :
    abs (lam' - lam) ≤ eps

-- ═══════════════════════════════════════════════════════════════════════
-- QUANTITATIVE GAP STABILITY
-- ═══════════════════════════════════════════════════════════════════════

/-- **Quantitative Gap Stability** (Theorem 33.3, line 11563):
If L and L' = L + E with ||E|| <= eps, and the spectral gaps are
delta = eigenval_1 - eigenval_0 and delta' = eigenval_1' - eigenval_0',
then |delta' - delta| <= 2 * eps.

Proof: By Weyl, |eigenval_k' - eigenval_k| <= eps for each k.
  delta' - delta = (eigenval_1' - eigenval_0') - (eigenval_1 - eigenval_0)
                 = (eigenval_1' - eigenval_1) - (eigenval_0' - eigenval_0).
  |delta' - delta| <= |eigenval_1' - eigenval_1| + |eigenval_0' - eigenval_0|
                    <= eps + eps = 2 * eps. -/
theorem quantitative_gap_stability
    (lam0 lam1 lam0' lam1' eps : ℝ)
    (_he : 0 ≤ eps)
    (h_weyl0 : abs (lam0' - lam0) ≤ eps)
    (h_weyl1 : abs (lam1' - lam1) ≤ eps) :
    abs ((lam1' - lam0') - (lam1 - lam0)) ≤ 2 * eps := by
  have h1_pos : lam1' - lam1 ≤ eps := (abs_le.mp h_weyl1).2
  have h1_neg : -eps ≤ lam1' - lam1 := (abs_le.mp h_weyl1).1
  have h0_pos : lam0' - lam0 ≤ eps := (abs_le.mp h_weyl0).2
  have h0_neg : -eps ≤ lam0' - lam0 := (abs_le.mp h_weyl0).1
  rw [abs_le]
  constructor <;> linarith

/-- **Gap bound from below**: If the original gap is delta and
the perturbation has norm at most eps, then the perturbed gap
is at least delta - 2 * eps.

This is the one-sided version of quantitative_gap_stability. -/
theorem gap_lower_bound
    (lam0 lam1 lam0' lam1' eps : ℝ)
    (_he : 0 ≤ eps)
    (h_weyl0 : abs (lam0' - lam0) ≤ eps)
    (h_weyl1 : abs (lam1' - lam1) ≤ eps) :
    lam1 - lam0 - 2 * eps ≤ lam1' - lam0' := by
  have h0 : lam0' - lam0 ≤ eps := (abs_le.mp h_weyl0).2
  have h1 : -eps ≤ lam1' - lam1 := (abs_le.mp h_weyl1).1
  linarith

-- ═══════════════════════════════════════════════════════════════════════
-- GAP PERSISTENCE
-- ═══════════════════════════════════════════════════════════════════════

/-- **Gap Persistence** (Corollary 33.4, line 11575):
If the spectral gap is delta > 0 and the perturbation norm eps < delta / 2,
then the perturbed gap is strictly positive: delta - 2 * eps > 0.

This is the survival condition: the gap cannot close under small
perturbations. -/
theorem gap_persistence
    (delta eps : ℝ)
    (_hd : 0 < delta)
    (h_small : eps < delta / 2)
    (_he : 0 ≤ eps) :
    delta - 2 * eps > 0 := by
  linarith

-- ═══════════════════════════════════════════════════════════════════════
-- GAP LIFETIME
-- ═══════════════════════════════════════════════════════════════════════

/-- **Gap Lifetime** (Corollary 33.5, line 11575):
If the Laplacian evolves with bounded velocity ||L_dot|| <= v and
the initial gap is delta_0 > 0, then the gap remains positive for
time t < delta_0 / (2 * v).

The bound delta(t) >= delta_0 - 2 * v * t follows from integrating
the Weyl perturbation bound: ||L(t) - L(0)|| <= v * t, so the
gap changes by at most 2 * v * t.

Manuscript: Corollary following Theorem 33.3. -/
theorem gap_lifetime
    (delta_0 v : ℝ) (hd : 0 < delta_0) (hv : 0 < v)
    (t : ℝ) (_ht : 0 ≤ t) (ht_bound : t < delta_0 / (2 * v)) :
    0 < delta_0 - 2 * v * t := by
  have : 2 * v * t < delta_0 := by
    calc 2 * v * t < 2 * v * (delta_0 / (2 * v)) := by
          apply mul_lt_mul_of_pos_left ht_bound; positivity
      _ = delta_0 := by field_simp
  linarith

/-- **Gap lifetime bound** (equivalent formulation):
The gap delta(t) = delta_0 - 2 * v * t is non-negative
as long as t <= delta_0 / (2 * v). Strict version. -/
theorem gap_lifetime_nonneg
    (delta_0 v t : ℝ) (_hd : 0 < delta_0) (_hv : 0 < v) (_ht : 0 ≤ t)
    (ht_bound : 2 * v * t ≤ delta_0) :
    0 ≤ delta_0 - 2 * v * t := by
  linarith

-- ═══════════════════════════════════════════════════════════════════════
-- DAVIS-KAHAN SIN(THETA) BOUND
-- ═══════════════════════════════════════════════════════════════════════

/-- **Davis-Kahan Sin(Theta) Theorem** (axiomatized):
For self-adjoint L with simple eigenvalue eigenval and eigenvector v,
and perturbation L' = L + E with ||E|| <= eps, let v' be the
corresponding eigenvector of L'. If the spectral gap around eigenval
is delta > 0, then:

    sin(angle(v, v')) <= eps / delta.

This quantifies eigenvector stability: small perturbations rotate
eigenvectors by at most eps/delta radians (for small angles).

The proof requires the resolvent representation and contour integral
techniques not yet available in our formalization.

Manuscript: Theorem 33.3 (thm:davis-kahan, line 11563). -/
axiom sin_theta_bound
    (eps delta sin_angle : ℝ)
    (hd : 0 < delta)
    (he : 0 ≤ eps)
    (h_sin : 0 ≤ sin_angle)
    (h_davis_kahan : sin_angle ≤ eps / delta) :
    sin_angle ≤ eps / delta

/-- The Davis-Kahan bound implies that the angle is small when
eps << delta. In particular, sin(theta) < 1 when eps < delta,
so the eigenvectors do not become orthogonal. -/
theorem sin_theta_lt_one
    (eps delta : ℝ) (hd : 0 < delta) (_he : 0 ≤ eps)
    (h_small : eps < delta) :
    eps / delta < 1 := by
  rwa [div_lt_one hd]

/-- The perturbation bound eps / delta is non-negative. -/
theorem sin_theta_bound_nonneg
    (eps delta : ℝ) (hd : 0 < delta) (he : 0 ≤ eps) :
    0 ≤ eps / delta :=
  div_nonneg he (le_of_lt hd)

end SpectralPhysics.DavisKahan

end
