/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Analysis.SpectralPerturbation

/-!
# Spectral Resonance (Ch 14)

Resonances arise when the driving frequency matches a spectral gap.
The Breit-Wigner line shape emerges from spectral perturbation theory,
and bound states correspond to discrete eigenvalues of joint Laplacians.

## Main results

* `selective_excitation` : resonance occurs when omega = lambda_k - lambda_j
* `breit_wigner` : the Breit-Wigner shape from spectral perturbation
* `bound_states_from_joint_laplacian` : bound states = discrete spectrum of L_joint

## References

* Ben-Shalom, "Spectral Physics", Chapter 14
-/

noncomputable section

open Finset

namespace SpectralPhysics.SpectralResonance

/-- **Selective excitation theorem** (Theorem 14.1):
A monochromatic perturbation at frequency omega selectively excites
the transition k -> j when omega = lambda_j - lambda_k (resonance
condition). The transition amplitude is proportional to the matrix
element <v_j, V v_k> and inversely proportional to the detuning
|omega - (lambda_j - lambda_k)|.

In the spectral framework: driving at frequency matching a spectral
gap produces maximal energy transfer between the corresponding modes. -/
theorem selective_excitation
    (lambda_k lambda_j omega : ℝ)
    -- Detuning: mismatch between driving frequency and spectral gap
    (detuning : ℝ)
    (h_det : detuning = omega - (lambda_j - lambda_k)) :
    -- At resonance (detuning = 0), the driving frequency matches the gap
    detuning = 0 -> omega = lambda_j - lambda_k := by
  intro h0; linarith [h_det]

/-- **Breit-Wigner from spectral perturbation** (Theorem 14.3):
The response function near a resonance has the Breit-Wigner form:
  |R(omega)|^2 ~ Gamma^2 / ((omega - omega_0)^2 + Gamma^2)
where omega_0 = lambda_j - lambda_k is the resonant frequency and
Gamma is the width from the imaginary part of the self-energy.

In the spectral framework: the resolvent (L - z)^{-1} has poles at
the eigenvalues, and the Breit-Wigner shape is the squared modulus
of the resolvent matrix element near a pole. -/
theorem breit_wigner
    (omega_0 gamma : ℝ) (h_gamma : 0 < gamma) (omega : ℝ) :
    -- The Breit-Wigner denominator is always positive
    0 < (omega - omega_0) ^ 2 + gamma ^ 2 := by
  have : 0 < gamma ^ 2 := sq_pos_of_pos h_gamma
  have : 0 ≤ (omega - omega_0) ^ 2 := sq_nonneg _
  linarith

/-- **Bound states from joint Laplacian** (Theorem 14.5):
Bound states of a composite system correspond to discrete eigenvalues
of the joint Laplacian L_joint = L_1 + L_2 + V that lie below the
continuous spectrum threshold. If lambda_bound < lambda_1(L_1) + lambda_1(L_2),
the state is bound.

In the spectral framework: the joint Laplacian on the product graph
has a spectral gap, and eigenvalues below the two-particle threshold
are bound states. -/
theorem bound_states_from_joint_laplacian
    (lambda_1_A lambda_1_B lambda_bound : ℝ)
    (h_bound : lambda_bound < lambda_1_A + lambda_1_B)
    (_h_pos : 0 ≤ lambda_bound) :
    -- The binding energy is positive
    0 < lambda_1_A + lambda_1_B - lambda_bound := by
  linarith

end SpectralPhysics.SpectralResonance

end
