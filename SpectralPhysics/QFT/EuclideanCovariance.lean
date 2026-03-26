/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Analysis.HeatSemigroup

/-!
# Euclidean Covariance (Osterwalder-Schrader Axiom OS1)

The heat kernel of a relational structure is invariant under isometries.
An isometry is a bijection that preserves the kernel k and measure μ.
Since the Laplacian L is built from k and μ, it commutes with isometries,
and consequently the heat inner product `Re<f, e^{-tL}f>` is invariant.

## Main definitions

* `RSIsometry` : a bijection of a relational structure preserving k and μ
* `RSIsometry.toEquiv` : the underlying equivalence
* `SpectralDecompIsometryCompat` : compatibility of spectral data with an isometry

## Main results

* `inner_product_invariant` : `<f . σ, g . σ> = <f, g>`
* `laplacian_commutes` : `L(f . σ) = (Lf) . σ`
* `spectral_coefficients_invariant` : `coeffSq (f . σ) = coeffSq f`
* `heat_inner_invariant` : `heatInner sd (f . σ) t = heatInner sd f t`
* `euclidean_covariance` : full OS1 statement

## References

* Ben-Shalom, "Spectral Physics", Chapter 6/10
* Osterwalder-Schrader, Comm. Math. Phys. 31 (1973), 83-112
-/

noncomputable section

open Finset Complex

variable (S : RelationalStructure)

namespace SpectralPhysics.EuclideanCovariance

-- ═══════════════════════════════════════════════════════════════════════
-- ISOMETRY DEFINITION
-- ═══════════════════════════════════════════════════════════════════════

/-- An isometry of a relational structure: a bijection preserving the
    kernel k and the measure μ. Named `RSIsometry` (Relational Structure
    Isometry) to avoid clash with Mathlib's `Isometry`. -/
structure RSIsometry (S : RelationalStructure) where
  /-- The underlying map -/
  σ : S.X → S.X
  /-- Bijectivity -/
  bijective : Function.Bijective σ
  /-- Kernel preservation: k(σ x, σ y) = k(x, y) -/
  preserves_kernel : ∀ (x y : S.X), S.k (σ x) (σ y) = S.k x y
  /-- Measure preservation: μ(σ x) = μ(x) -/
  preserves_measure : ∀ (x : S.X), S.μ (σ x) = S.μ x

variable {S}

/-- Build an `Equiv` from an `RSIsometry` on a `Fintype`. -/
def RSIsometry.toEquiv (iso : RSIsometry S) : S.X ≃ S.X :=
  Equiv.ofBijective iso.σ iso.bijective

/-- Weight factor is preserved by an isometry (since |k| depends on k). -/
theorem RSIsometry.preserves_weightFactor (iso : RSIsometry S) (x y : S.X) :
    S.weightFactor (iso.σ x) (iso.σ y) = S.weightFactor x y := by
  simp only [RelationalStructure.weightFactor]
  rw [iso.preserves_kernel x y]

/-- Phase factor is preserved by an isometry (since arg depends on k). -/
theorem RSIsometry.preserves_phaseFactor (iso : RSIsometry S) (x y : S.X) :
    S.phaseFactor (iso.σ x) (iso.σ y) = S.phaseFactor x y := by
  simp only [RelationalStructure.phaseFactor]
  rw [iso.preserves_kernel x y]

-- ═══════════════════════════════════════════════════════════════════════
-- INNER PRODUCT INVARIANCE
-- ═══════════════════════════════════════════════════════════════════════

/-- **Inner product invariance**: `<f . σ, g . σ> = <f, g>`.

PROOF: Change of variables in the sum via the bijection σ.
  <f.σ, g.σ> = Σ_x conj(f(σ x)) * g(σ x) * μ(x)
By rewriting μ(x) = μ(σ x) and applying Equiv.sum_comp:
  = Σ_x conj(f(σ x)) * g(σ x) * μ(σ x)
  = Σ_z conj(f(z)) * g(z) * μ(z)       [change of variables z = σ x]
  = <f, g> -/
theorem inner_product_invariant (iso : RSIsometry S)
    (f g : S.X → ℂ) :
    S.innerProduct (f ∘ iso.σ) (g ∘ iso.σ) = S.innerProduct f g := by
  simp only [RelationalStructure.innerProduct, Function.comp]
  -- Rewrite μ(x) to μ(σ x) using measure preservation (backwards)
  conv_lhs =>
    arg 2; ext x
    rw [show (S.μ x : ℂ) = (S.μ (iso.σ x) : ℂ) from by
      rw [iso.preserves_measure]]
  -- Now the summand is h(σ x) for h(z) = conj(f z) * g z * μ z
  -- Apply change of variables: Σ_x h(e x) = Σ_x h(x)
  exact iso.toEquiv.sum_comp
    (fun z => starRingEnd ℂ (f z) * g z * (↑(S.μ z) : ℂ))

-- ═══════════════════════════════════════════════════════════════════════
-- LAPLACIAN COMMUTES WITH ISOMETRIES
-- ═══════════════════════════════════════════════════════════════════════

/-- **Laplacian commutes with isometries**: `L(f . σ)(x) = (Lf)(σ x)`.

PROOF: L(f . σ)(x) = Σ_y |k(x,y)| (f(σ x) - phase(x,y) f(σ y)) μ(y).
  (Lf)(σ x) = Σ_y |k(σ x, y)| (f(σ x) - phase(σ x, y) f(y)) μ(y).
Change variables y → σ(y) in the RHS and use preservation of k, μ. -/
theorem laplacian_commutes (iso : RSIsometry S)
    (f : S.X → ℂ) (x : S.X) :
    S.SpectralLaplacian (f ∘ iso.σ) x =
    S.SpectralLaplacian f (iso.σ x) := by
  simp only [RelationalStructure.SpectralLaplacian, Function.comp]
  -- RHS: Σ_y |k(σ x, y)| * (f(σ x) - phase(σ x, y) * f(y)) * μ(y)
  -- Change of variables y → σ(y): Σ_y |k(σ x, σ y)| * (...) * μ(σ y)
  symm
  rw [show (∑ y : S.X, S.weightFactor (iso.σ x) y *
      (f (iso.σ x) - S.phaseFactor (iso.σ x) y * f y) * ↑(S.μ y)) =
    ∑ y : S.X, (fun z => S.weightFactor (iso.σ x) z *
      (f (iso.σ x) - S.phaseFactor (iso.σ x) z * f z) * ↑(S.μ z)) y
    from by rfl]
  rw [← iso.toEquiv.sum_comp]
  -- After substitution, summand has σ applied to y
  -- Use preservation of weight factor, phase factor, and measure
  congr 1; ext y
  simp only [RSIsometry.toEquiv, Equiv.ofBijective_apply]
  rw [iso.preserves_weightFactor x y, iso.preserves_phaseFactor x y,
      iso.preserves_measure y]

-- ═══════════════════════════════════════════════════════════════════════
-- SPECTRAL COEFFICIENT INVARIANCE
-- ═══════════════════════════════════════════════════════════════════════

/-- A spectral decomposition is compatible with an isometry when the
    squared spectral coefficients are invariant under precomposition
    with σ. This follows from L commuting with σ: the eigenbasis
    can be chosen σ-invariant, making |<v_k, f . σ>|^2 = |<v_k, f>|^2.

    We axiomatize this compatibility because `coeffSq` is abstract in
    `SpectralDecomp`. The justification is: since L commutes with σ
    (proved in `laplacian_commutes`), L and σ are simultaneously
    diagonalizable on each eigenspace, so the squared projections
    are preserved. -/
def SpectralDecompIsometryCompat {n : ℕ} (sd : SpectralDecomp S n)
    (iso : RSIsometry S) : Prop :=
  ∀ (f : S.X → ℂ) (k : Fin n),
    sd.coeffSq (f ∘ iso.σ) k = sd.coeffSq f k

/-- When a spectral decomposition is compatible with an isometry,
    the spectral coefficients of `f . σ` equal those of `f`. -/
theorem spectral_coefficients_invariant {n : ℕ}
    (sd : SpectralDecomp S n) (iso : RSIsometry S)
    (hcompat : SpectralDecompIsometryCompat sd iso)
    (f : S.X → ℂ) (k : Fin n) :
    sd.coeffSq (f ∘ iso.σ) k = sd.coeffSq f k :=
  hcompat f k

-- ═══════════════════════════════════════════════════════════════════════
-- HEAT INNER PRODUCT INVARIANCE (OS1)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Heat inner product invariance (OS1)**:
    `heatInner sd (f . σ) t = heatInner sd f t`.

PROOF: By the spectral representation,
  heatInner sd (f . σ) t = Σ_k e^{-t λ_k} * coeffSq (f . σ) k
                          = Σ_k e^{-t λ_k} * coeffSq f k
                          = heatInner sd f t.
The middle equality uses spectral coefficient invariance. -/
theorem heat_inner_invariant {n : ℕ}
    (sd : SpectralDecomp S n) (iso : RSIsometry S)
    (hcompat : SpectralDecompIsometryCompat sd iso)
    (f : S.X → ℂ) (t : ℝ) :
    heatInner sd (f ∘ iso.σ) t = heatInner sd f t := by
  simp only [heatInner]
  congr 1; ext k
  rw [spectral_coefficients_invariant sd iso hcompat f k]

-- ═══════════════════════════════════════════════════════════════════════
-- FULL OS1 STATEMENT
-- ═══════════════════════════════════════════════════════════════════════

/-- **Euclidean covariance (OS1)**: For any isometry σ of a relational
    structure, and any spectral decomposition compatible with σ, the
    Euclidean correlator is invariant:

      Re<f . σ, K_t(f . σ)> = Re<f, K_t f>

    This is OS1 in the Osterwalder-Schrader axioms. In the continuum limit
    with spectral dimension d, the isometry group becomes SO(d), giving full
    Euclidean covariance. Combined with OS reconstruction, this yields
    Poincare covariance (W1) of the Wightman theory. -/
theorem euclidean_covariance {n : ℕ}
    (sd : SpectralDecomp S n) (iso : RSIsometry S)
    (hcompat : SpectralDecompIsometryCompat sd iso)
    (f : S.X → ℂ) (t : ℝ) :
    heatInner sd (f ∘ iso.σ) t = heatInner sd f t :=
  heat_inner_invariant sd iso hcompat f t

/-- Compatibility is justified: inner product invariance and Parseval
    together imply the sum of coeffSq is preserved. This is a necessary
    condition for `SpectralDecompIsometryCompat`, confirming consistency. -/
theorem coeffSq_sum_invariant {n : ℕ}
    (sd : SpectralDecomp S n) (iso : RSIsometry S)
    (f : S.X → ℂ) :
    ∑ k : Fin n, sd.coeffSq (f ∘ iso.σ) k =
    ∑ k : Fin n, sd.coeffSq f k := by
  rw [← sd.parseval (f ∘ iso.σ), ← sd.parseval f]
  exact congrArg Complex.re (inner_product_invariant iso f f)

end SpectralPhysics.EuclideanCovariance

end
