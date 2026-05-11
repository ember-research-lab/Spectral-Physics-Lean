/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.CompositionUniqueness.HypothesisSet

/-!
# Additive Convolution Satisfies All Three Conditions

* Hamiltonian additivity: direct from `trace_additiveConv`.
* Hurwitz compatibility: witness the `max`-style level assignment.
* Faithfulness: `card_additiveConv` gives cardinality
  multiplicativity; left/right Minkowski cancellation is packaged
  as two named axioms (cited to Lev-Yuster 1999; Nathanson 1996;
  Tao-Vu 2006).

## Honest scope of the named axioms

The two `minkowski_*_cancel` axioms are **generic algebraic facts
about Minkowski sums of multisets**, true for *all* non-trivial
multisets — they are NOT assertions of any conclusion of this
module.  They are introduced here only because Mathlib's
`Multiset` API does not yet expose cancellation under
`bind`-with-shift.

## References

* Lev, V., Yuster, R., "Restricted set addition in groups, I",
  *J. Algebra* 211 (1999).
* Nathanson, *Additive Number Theory* (Springer GTM 165, 1996),
  Ch. 1.
* Tao, T., Vu, V., *Additive Combinatorics* (Cambridge SAM 105,
  2006), §2.4.
* Reed-Simon I, §VIII.10.
-/

namespace SpectralPhysics.CompositionUniqueness

open BinaryOpOnSpectra

/-! ## Hamiltonian additivity — direct from `trace_additiveConv` -/

theorem additive_satisfies_hamiltonian :
    HamiltonianAdditivity additive := by
  intro μ ν
  rw [additive_apply, trace_additiveConv]

/-! ## Hurwitz compatibility — witness the `max`-style assignment -/

/-- The "take the higher level" Hurwitz pairing. -/
def HurwitzLevel.sup : HurwitzLevel → HurwitzLevel → HurwitzLevel
  | .reals,   j        => j
  | i,        .reals   => i
  | .complex, .complex => .complex
  | .complex, .quat    => .quat
  | .complex, .oct     => .oct
  | .quat,    .complex => .quat
  | .quat,    .quat    => .quat
  | .quat,    .oct     => .oct
  | .oct,     .complex => .oct
  | .oct,     .quat    => .oct
  | .oct,     .oct     => .oct

@[simp] lemma HurwitzLevel.sup_reals_left (i : HurwitzLevel) :
    HurwitzLevel.sup .reals i = i := by
  cases i <;> rfl

@[simp] lemma HurwitzLevel.sup_reals_right (i : HurwitzLevel) :
    HurwitzLevel.sup i .reals = i := by
  cases i <;> rfl

theorem additive_satisfies_hurwitz :
    HurwitzCompatibility additive :=
  ⟨⟨HurwitzLevel.sup, HurwitzLevel.sup_reals_left,
    HurwitzLevel.sup_reals_right⟩⟩

/-! ## Faithfulness — cardinality + two named Minkowski axioms -/

/-- **Named axiom (Minkowski left cancellation for multisets of reals)**.
Standard additive-combinatorics result.

**Citation**: Lev-Yuster (1999); Nathanson (1996) Ch. 1; Tao-Vu
(2006) §2.4. -/
axiom minkowski_left_cancel :
    ∀ μ μ' ν : Spectrum, ν.NonTrivial →
      additiveConv μ ν = additiveConv μ' ν → μ = μ'

/-- **Named axiom (Minkowski right cancellation, symmetric form)**.
Same citation as `minkowski_left_cancel`. -/
axiom minkowski_right_cancel :
    ∀ μ ν ν' : Spectrum, μ.NonTrivial →
      additiveConv μ ν = additiveConv μ ν' → ν = ν'

theorem additive_satisfies_faithfulness :
    PreservesFaithfulness additive where
  card_mul := by
    intro μ ν
    simp [additive_apply, card_additiveConv]
  left_cancel := by
    intro μ μ' ν hν h
    simp only [additive_apply] at h
    exact minkowski_left_cancel μ μ' ν hν h
  right_cancel := by
    intro μ ν ν' hμ h
    simp only [additive_apply] at h
    exact minkowski_right_cancel μ ν ν' hμ h

/-- **Bundled theorem**: additive convolution satisfies all three
conditions (modulo the two cited Minkowski-cancellation axioms). -/
theorem additive_satisfies_three_conditions :
    ThreeConditions additive where
  hamilton := additive_satisfies_hamiltonian
  hurwitz  := additive_satisfies_hurwitz
  faithful := additive_satisfies_faithfulness

end SpectralPhysics.CompositionUniqueness
