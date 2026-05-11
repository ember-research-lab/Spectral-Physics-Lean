/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.CompositionUniqueness.HypothesisSet

/-!
# Free Convolution Placeholder Violates Hamiltonian Additivity

The `freeConv` placeholder from `SpectralOperations.lean` returns
the empty spectrum on every input.  The trace of the empty
spectrum is `0`, but Hamiltonian-additivity on the witness pair
`{2}, {3}` demands `5`, so the placeholder falsifies the trace
identity.  Zero new axioms.

## Honest scope

The `freeConv` placeholder is **not** Voiculescu's free
convolution.  See the docstring of
`SpectralOperations.lean` for what the placeholder *is* and is
not.  We do not axiomatise any algebra-level statement about
genuine free convolution in this branch.

## References

* Voiculescu (1985); VDN (1992); Hurwitz (1898)
-/

namespace SpectralPhysics.CompositionUniqueness

open BinaryOpOnSpectra

@[simp] lemma freeConv_eq_zero (μ ν : Spectrum) :
    freeConv μ ν = (0 : Spectrum) := rfl

@[simp] lemma trace_freeConv (μ ν : Spectrum) :
    Spectrum.trace (freeConv μ ν) = 0 := by
  simp [freeConv, Spectrum.trace]

/-- **Theorem**: the `freeConv` placeholder fails Hamiltonian
additivity (witness: `{2}, {3}`; `0 ≠ 5`). -/
theorem free_violates_hamiltonian_additivity :
    ¬ HamiltonianAdditivity BinaryOpOnSpectra.free := by
  intro h
  have hμν := h ({2} : Multiset ℝ) ({3} : Multiset ℝ)
  simp only [free_apply, trace_freeConv] at hμν
  have h_c2 : (Multiset.card ({2} : Multiset ℝ) : ℝ) = 1 := by simp
  have h_c3 : (Multiset.card ({3} : Multiset ℝ) : ℝ) = 1 := by simp
  have h_t2 : Spectrum.trace ({2} : Multiset ℝ) = 2 := by
    unfold Spectrum.trace; simp
  have h_t3 : Spectrum.trace ({3} : Multiset ℝ) = 3 := by
    unfold Spectrum.trace; simp
  rw [h_c2, h_c3, h_t2, h_t3] at hμν
  norm_num at hμν

/-- **Corollary**: the `freeConv` placeholder does not satisfy the
full three-condition bundle. -/
theorem free_not_three_conditions :
    ¬ ThreeConditions BinaryOpOnSpectra.free := by
  intro h
  exact free_violates_hamiltonian_additivity h.hamilton

end SpectralPhysics.CompositionUniqueness
