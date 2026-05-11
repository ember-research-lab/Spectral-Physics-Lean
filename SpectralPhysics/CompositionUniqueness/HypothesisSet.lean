/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.CompositionUniqueness.SpectralOperations

/-!
# The Hypothesis Set for Composition Uniqueness

Defines `BinaryOpOnSpectra`, the three condition predicates
(`HamiltonianAdditivity`, `HurwitzCompatibility`,
`PreservesFaithfulness`), and the bundled `ThreeConditions`.

## Honest scope of the predicates

* `HamiltonianAdditivity` is genuinely the trace identity for the
  additive lift (Reed-Simon I, §VIII.10).
* `HurwitzCompatibility` is the **existence** of any
  level-assignment `HurwitzLevel × HurwitzLevel → HurwitzLevel`
  acting as identity when one factor is `ℝ`.  This is a deliberately
  weak spectrum-level shadow — it does NOT encode the genuine
  Cayley-Dickson doubling condition.  See the docstring of
  `Algebra/Hurwitz.lean` for the algebra-level version.
* `PreservesFaithfulness` is cardinality multiplicativity plus
  left/right Minkowski cancellation.

## What this file does NOT claim

It does NOT claim that satisfying these three predicates forces
the operation to equal additive convolution pointwise as a
multiset.  See `BroaderUniquenessOpen.lean` for the open
broader-uniqueness predicate, and `KasparovProductUniqueness.lean`
for the narrow Kasparov-product theorem.

## References

* Hurwitz (1898), Reed-Simon I §VIII.10
* v0.9 manuscript line 16783 (the hand-wavy admission)
-/

namespace SpectralPhysics.CompositionUniqueness

/-! ## The four rungs of the Hurwitz tower -/

/-- The four levels of the Cayley-Dickson tower (Hurwitz's theorem). -/
inductive HurwitzLevel : Type
  | reals
  | complex
  | quat
  | oct
  deriving DecidableEq, Repr

/-- A `HurwitzLevelAssignment` records a way of pairing two Hurwitz
levels into a third, acting as identity when one factor is `ℝ`. -/
structure HurwitzLevelAssignment where
  toFun  : HurwitzLevel → HurwitzLevel → HurwitzLevel
  unit_left  : ∀ i, toFun .reals i = i
  unit_right : ∀ i, toFun i .reals = i

/-! ## The type of a candidate composition law -/

/-- A `BinaryOpOnSpectra` is a binary operation on `Spectrum`. -/
@[ext]
structure BinaryOpOnSpectra where
  toFun : Spectrum → Spectrum → Spectrum

namespace BinaryOpOnSpectra

instance : CoeFun BinaryOpOnSpectra (fun _ => Spectrum → Spectrum → Spectrum) :=
  ⟨BinaryOpOnSpectra.toFun⟩

/-- Additive operation on spectra. -/
def additive : BinaryOpOnSpectra := ⟨additiveConv⟩

/-- Multiplicative operation on spectra. -/
def multiplicative : BinaryOpOnSpectra := ⟨multiplicativeConv⟩

/-- Free operation placeholder. -/
def free : BinaryOpOnSpectra := ⟨freeConv⟩

@[simp] lemma additive_apply (μ ν : Spectrum) :
    additive μ ν = additiveConv μ ν := rfl

@[simp] lemma multiplicative_apply (μ ν : Spectrum) :
    multiplicative μ ν = multiplicativeConv μ ν := rfl

@[simp] lemma free_apply (μ ν : Spectrum) :
    free μ ν = freeConv μ ν := rfl

end BinaryOpOnSpectra

/-! ## The three condition predicates -/

/-- **Hamiltonian additivity** (necessary trace-level condition
for a non-interacting composite Hamiltonian; Reed-Simon I,
§VIII.10). -/
def HamiltonianAdditivity (op : BinaryOpOnSpectra) : Prop :=
  ∀ μ ν : Spectrum,
    Spectrum.trace (op μ ν) =
      (Multiset.card ν : ℝ) * Spectrum.trace μ +
        (Multiset.card μ : ℝ) * Spectrum.trace ν

/-- **Hurwitz-tower compatibility (spectrum-level shadow)**:
existence of any `HurwitzLevelAssignment`.  Deliberately weak —
see file docstring. -/
def HurwitzCompatibility (_op : BinaryOpOnSpectra) : Prop :=
  Nonempty HurwitzLevelAssignment

/-- **Faithfulness preservation**: cardinality multiplicativity
plus left/right Minkowski cancellation. -/
structure PreservesFaithfulness (op : BinaryOpOnSpectra) : Prop where
  card_mul :
    ∀ μ ν : Spectrum,
      Multiset.card (op μ ν) = Multiset.card μ * Multiset.card ν
  left_cancel :
    ∀ μ μ' ν : Spectrum, ν.NonTrivial →
      op μ ν = op μ' ν → μ = μ'
  right_cancel :
    ∀ μ ν ν' : Spectrum, μ.NonTrivial →
      op μ ν = op μ ν' → ν = ν'

/-- **The bundle**: all three conditions together. -/
structure ThreeConditions (op : BinaryOpOnSpectra) : Prop where
  hamilton  : HamiltonianAdditivity op
  hurwitz   : HurwitzCompatibility op
  faithful  : PreservesFaithfulness op

end SpectralPhysics.CompositionUniqueness
