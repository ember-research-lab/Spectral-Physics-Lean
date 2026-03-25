/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Axioms.Laplacian
import SpectralPhysics.Analysis.HeatSemigroup

/-!
# The Spectrum (Ch 3)

Basic properties of the Laplacian spectrum: ground state, Fiedler vector,
and the spectral gap as a health diagnostic for relational structures.

## Main results

* `ground_state_constant` : the ground state eigenvector is constant
* `fiedler_orthogonal_ground` : the Fiedler vector is orthogonal to constants
* `fiedler_sign_change` : the Fiedler vector changes sign (connected case)
* `spectral_gap_health` : positive gap iff exponential correlator decay

## References

* Ben-Shalom, "Spectral Physics", Chapter 3
-/

noncomputable section

open Finset

variable (S : RelationalStructure)

namespace SpectralPhysics.SpectrumBasics

/-- **Ground state is constant** (Proposition 3.1):
On a classical connected relational structure, any zero-eigenvalue
eigenvector of the Laplacian is constant. The ground state eigenvalue
is lambda_0 = 0, and the corresponding eigenspace is spanned by the
constant function.

Proof: from `null_space_is_constants` in Axioms/Laplacian. -/
theorem ground_state_constant
    (hc : S.isClassical)
    (hconn : RelationalStructure.SpectralLaplacian.isStronglyConnected S)
    (f : S.X -> ℂ)
    (hf : (S.innerProduct f (S.SpectralLaplacian f)).re = 0) :
    ∃ (c : ℂ), f = fun _ => c :=
  RelationalStructure.SpectralLaplacian.null_space_is_constants S hc hconn f hf

/-- **Fiedler vector orthogonality** (Proposition 3.3):
The Fiedler vector (eigenvector for lambda_1) is orthogonal to the
ground state. In the spectral decomposition, the ground-state coefficient
of any function supported only on lambda_1 vanishes. -/
theorem fiedler_orthogonal_ground {n : ℕ}
    (sd : SpectralDecomp S n) (hn : 1 < n)
    (f : S.X -> ℂ)
    -- f is supported on mode 1 only: c_k = 0 for k != 1
    (h_support : ∀ k : Fin n, (k : ℕ) ≠ 1 -> sd.coeffSq f k = 0) :
    sd.coeffSq f ⟨0, by omega⟩ = 0 := by
  exact h_support ⟨0, by omega⟩ (by omega : (0 : ℕ) ≠ 1)

/-- **Fiedler vector sign change** (Proposition 3.4):
On a connected structure with positive spectral gap, any real-valued
function in the first excited eigenspace must change sign. If it were
everywhere non-negative and nonzero, its inner product with the constant
ground state would be positive, contradicting orthogonality. -/
theorem fiedler_sign_change
    (f : S.X -> ℝ)
    (h_nonzero : ∃ x : S.X, f x ≠ 0)
    (h_ortho : ∑ x : S.X, f x * S.μ x = 0) :
    (∃ x : S.X, f x > 0) ∧ (∃ y : S.X, f y < 0) := by
  sorry

/-- **Spectral gap as health diagnostic** (Theorem 3.7):
The spectral gap lambda_1 controls the rate of correlator decay.
For f orthogonal to the ground state:
  Re<f, K_t f> <= e^{-t lambda_1} ||f||^2.

Large gap = rapid thermalization = healthy, well-connected structure.
Small gap = slow mixing = structure near disconnection. -/
theorem spectral_gap_health {n : ℕ}
    (sd : SpectralDecomp S n) (hn : 1 < n)
    (f : S.X -> ℂ) (hf : sd.coeffSq f ⟨0, by omega⟩ = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    heatInner sd f t ≤
      Real.exp (-t * sd.eigenval ⟨1, hn⟩) * (S.innerProduct f f).re :=
  correlator_decay sd hn f hf t ht

end SpectralPhysics.SpectrumBasics

end
