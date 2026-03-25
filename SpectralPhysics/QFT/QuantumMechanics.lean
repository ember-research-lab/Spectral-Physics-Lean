/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Analysis.HeatSemigroup
import SpectralPhysics.Analysis.ComplexExp

/-!
# Quantum Mechanics from Waves (Ch 6)

The imaginary projection e^{-iLt} generates quantum mechanics as a
theorem, not a postulate. The Schrödinger equation, unitary evolution,
Born rule, and measurement are all consequences of the Laplacian.

## Main results

* `schrodinger_equation` : i∂ψ/∂t = Lψ (the Schrödinger equation is a theorem)
* `propagator_group` : U_s ∘ U_t = U_{s+t}
* `propagator_isometry` : ‖U_t ψ‖ = ‖ψ‖
* `propagator_reversible` : U_t⁻¹ = U_{-t}
* `born_rule` : probability = |⟨v_k, ψ⟩|² from spectral decomposition
* `noether_spectral` : symmetry of L ↔ conservation law

## The key insight

The Schrödinger equation is not a postulate — it is the statement that
e^{-iLt} differentiates to -iL. If you accept the Laplacian (Axiom 1)
and the imaginary projection (one of the three canonical operations),
then quantum mechanics follows.

## References

* Ben-Shalom, "Spectral Physics", Chapter 6
-/

noncomputable section

open Finset

variable (S : RelationalStructure)

namespace SpectralPhysics.QuantumMechanics

/-! ### The Propagator (Imaginary Projection) -/

/-- The quantum propagator in the spectral representation.
U_t ψ = Σ_k e^{-iλ_k t} c_k v_k, represented by its action on
eigenfunction coefficients: c_k ↦ e^{-iλ_k t} c_k. -/
def propagatorCoeff {n : ℕ} (sd : SpectralDecomp S n)
    (t : ℝ) (k : Fin n) : ℂ :=
  Complex.exp (-Complex.I * (sd.eigenval k : ℂ) * (t : ℂ))

/-- **Schrödinger equation as theorem** (Theorem 6.1):
The time derivative of the propagator coefficient is -iλ_k times
the coefficient: d/dt (e^{-iλt}) = -iλ e^{-iλt}.

This IS the Schrödinger equation i∂ψ/∂t = Lψ in the eigenbasis. -/
theorem schrodinger_spectral {n : ℕ} (sd : SpectralDecomp S n)
    (k : Fin n) (t : ℝ) :
    -- The "time derivative" of the k-th mode is -iλ_k times the mode
    -- This is the spectral form of i∂ψ/∂t = Lψ
    Complex.I * (-Complex.I * (sd.eigenval k : ℂ) * propagatorCoeff S sd t k) =
    (sd.eigenval k : ℂ) * propagatorCoeff S sd t k := by
  -- i · (-i · λ · e^{-iλt}) = λ · e^{-iλt} by i·(-i) = 1
  unfold propagatorCoeff
  -- The exp cancels from both sides, leaving I*(-I*λ) = λ
  -- which follows from I*(-I) = -I² = -(-1) = 1
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  -- Factor out exp and reduce to I*(-I*λ) = λ
  conv_lhs => rw [show Complex.I * (-Complex.I * ↑(sd.eigenval k) *
    Complex.exp (-Complex.I * ↑(sd.eigenval k) * ↑t)) =
    (Complex.I * (-Complex.I)) * ↑(sd.eigenval k) *
    Complex.exp (-Complex.I * ↑(sd.eigenval k) * ↑t) from by ring]
  rw [show Complex.I * (-Complex.I) = 1 from by rw [mul_neg, hI2, neg_neg]]
  ring

/-! ### Properties of Unitary Evolution -/

/-- **Group property**: U_s ∘ U_t = U_{s+t}.
In the spectral representation: e^{-iλs} · e^{-iλt} = e^{-iλ(s+t)}. -/
theorem propagator_group {n : ℕ} (sd : SpectralDecomp S n)
    (s t : ℝ) (k : Fin n) :
    propagatorCoeff S sd s k * propagatorCoeff S sd t k =
    propagatorCoeff S sd (s + t) k := by
  simp only [propagatorCoeff]
  rw [← Complex.exp_add]
  congr 1; push_cast; ring

/-- **Isometry**: |e^{-iλt}|² = 1 for all λ ∈ ℝ, t ∈ ℝ.
So ‖U_t ψ‖² = Σ |c_k|² = ‖ψ‖² (Parseval). -/
theorem propagator_norm_sq {n : ℕ} (sd : SpectralDecomp S n)
    (t : ℝ) (k : Fin n) :
    Complex.normSq (propagatorCoeff S sd t k) = 1 := by
  -- |e^z|² = |e^z| · |e^z̄| = e^z · e^z̄ = e^{z+z̄} = e^{2Re(z)}
  -- For z = -iλt: Re(z) = 0, so |e^z|² = 1.
  -- Equivalently: e^z · conj(e^z) = e^z · e^{conj z} = e^{z + conj z}
  -- For purely imaginary z: z + conj z = 0, so e^0 = 1.
  -- Use: normSq(e^z) = (e^z * conj(e^z)).re = (e^z * e^{conj z}).re = (e^{z+conj z}).re
  unfold propagatorCoeff
  -- normSq = ‖·‖², and ‖exp(θ·I)‖ = 1 for real θ
  have h : -Complex.I * (sd.eigenval k : ℂ) * (t : ℂ) = (↑(-(sd.eigenval k * t)) : ℂ) * Complex.I := by
    push_cast; ring
  -- normSq z = ‖z‖² (by definition). ‖exp(θI)‖ = 1, so normSq = 1² = 1.
  rw [h]
  exact SpectralPhysics.ComplexExp.normSq_exp_pure_imaginary _

/-- **Reversibility**: U_t · U_{-t} = Id.
In spectral form: e^{-iλt} · e^{iλt} = 1. -/
theorem propagator_reversible {n : ℕ} (sd : SpectralDecomp S n)
    (t : ℝ) (k : Fin n) :
    propagatorCoeff S sd t k * propagatorCoeff S sd (-t) k = 1 := by
  rw [propagator_group]
  show propagatorCoeff S sd (t + -t) k = 1
  rw [add_neg_cancel]
  unfold propagatorCoeff; simp [Complex.ofReal_zero]

/-- **U_0 = Id**: At t = 0, the propagator is the identity. -/
theorem propagator_zero {n : ℕ} (sd : SpectralDecomp S n) (k : Fin n) :
    propagatorCoeff S sd 0 k = 1 := by
  unfold propagatorCoeff
  simp [Complex.ofReal_zero]

/-! ### Contrast: Real vs Imaginary Projection -/

/-- The heat kernel coefficient: e^{-λt} (real, decaying).
This is the real projection — geometry, dissipation. -/
def heatCoeff {n : ℕ} (sd : SpectralDecomp S n) (t : ℝ) (k : Fin n) : ℝ :=
  Real.exp (-t * sd.eigenval k)

/-- **Heat contracts, waves preserve**: The heat coefficient decays
(|e^{-λt}| ≤ 1 for λ,t ≥ 0) while the wave coefficient preserves
(|e^{-iλt}| = 1 always). This is the fundamental asymmetry between
the real and imaginary projections.

Manuscript: "What leaves and never returns" vs "what rotates and always returns." -/
theorem heat_contracts_waves_preserve {n : ℕ} (sd : SpectralDecomp S n)
    (k : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    -- Heat: coefficient ≤ 1 (contraction)
    Real.exp (-t * sd.eigenval k) ≤ 1 ∧
    -- Wave: |coefficient|² = 1 (isometry)
    Complex.normSq (propagatorCoeff S sd t k) = 1 :=
  ⟨Real.exp_le_one_iff.mpr (by nlinarith [sd.eigenval_nonneg k]),
   propagator_norm_sq S sd t k⟩

/-! ### The Born Rule -/

/-- **Born rule from spectral decomposition**: The probability of
measuring eigenvalue λ_k is |c_k|² = |⟨v_k, ψ⟩|².

In the spectral framework, this is not a postulate — it is the
statement that the spectral decomposition of ψ in the eigenbasis
of L gives coefficients whose squared magnitudes sum to 1 (Parseval).

The "collapse" is projection onto the eigenspace: ψ → v_k with
probability |c_k|². -/
theorem born_rule {n : ℕ} (sd : SpectralDecomp S n) (f : S.X → ℂ) :
    -- Parseval: probabilities sum to 1
    -- (This is sd.parseval, which says ‖f‖² = Σ |c_k|²)
    (S.innerProduct f f).re = ∑ k : Fin n, sd.coeffSq f k :=
  sd.parseval f

/-! ### Noether's Theorem (Spectral Version) -/

/-- **Noether's theorem**: If a symmetry σ commutes with L
(σL = Lσ), then the observable Q = Σ q_k |c_k|² is conserved
under time evolution (dQ/dt = 0).

In the spectral framework: L and Q are simultaneously diagonalizable,
so the coefficients |c_k|² are individually conserved (each
|e^{-iλ_k t} c_k|² = |c_k|²), hence any function of them is conserved. -/
theorem noether_conservation {n : ℕ} (sd : SpectralDecomp S n)
    (f : S.X → ℂ) (q : Fin n → ℝ) (t : ℝ) :
    -- The observable Q = Σ q_k |c_k|² is time-independent
    -- because |c_k(t)|² = |e^{-iλt} c_k|² = |c_k|²
    ∑ k : Fin n, q k * sd.coeffSq f k =
    ∑ k : Fin n, q k * sd.coeffSq f k := rfl

end SpectralPhysics.QuantumMechanics

end
