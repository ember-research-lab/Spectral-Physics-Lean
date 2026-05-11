/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.CompositionUniqueness.HypothesisSet

/-!
# Multiplicative Convolution Violates Hamiltonian Additivity

Concrete spectrum-level falsifier with witness `μ₀ = {2}`,
`ν₀ = {3}`: `Tr (μ₀ ⊠ ν₀) = 6 ≠ 5 = |ν₀|·Tr μ₀ + |μ₀|·Tr ν₀`.
Zero new axioms.

## References

* Reed-Simon I, §VIII.10
-/

namespace SpectralPhysics.CompositionUniqueness

open BinaryOpOnSpectra

/-- Witness multiset on the left: a single eigenvalue of value 2. -/
private def μ₀ : Spectrum := ({2} : Multiset ℝ)

/-- Witness multiset on the right: a single eigenvalue of value 3. -/
private def ν₀ : Spectrum := ({3} : Multiset ℝ)

@[simp] private lemma card_μ₀ : Multiset.card μ₀ = 1 := by
  unfold μ₀; simp

@[simp] private lemma card_ν₀ : Multiset.card ν₀ = 1 := by
  unfold ν₀; simp

@[simp] private lemma trace_μ₀ : Spectrum.trace μ₀ = 2 := by
  unfold μ₀ Spectrum.trace; simp

@[simp] private lemma trace_ν₀ : Spectrum.trace ν₀ = 3 := by
  unfold ν₀ Spectrum.trace; simp

private lemma counterexample_separates :
    Spectrum.trace (multiplicativeConv μ₀ ν₀) ≠
      (Multiset.card ν₀ : ℝ) * Spectrum.trace μ₀ +
        (Multiset.card μ₀ : ℝ) * Spectrum.trace ν₀ := by
  rw [trace_multiplicativeConv]
  simp only [card_μ₀, card_ν₀, trace_μ₀, trace_ν₀, Nat.cast_one]
  norm_num

/-- **Theorem**: multiplicative convolution does not satisfy
Hamiltonian additivity (witness: `{2}, {3}`; `6 ≠ 5`). -/
theorem multiplicative_violates_hamiltonian_additivity :
    ¬ HamiltonianAdditivity multiplicative := by
  intro h
  have hμν := h μ₀ ν₀
  simp only [multiplicative_apply] at hμν
  exact counterexample_separates hμν

/-- **Corollary**: multiplicative convolution does not satisfy the
full three-condition bundle. -/
theorem multiplicative_not_three_conditions :
    ¬ ThreeConditions multiplicative := by
  intro h
  exact multiplicative_violates_hamiltonian_additivity h.hamilton

end SpectralPhysics.CompositionUniqueness
