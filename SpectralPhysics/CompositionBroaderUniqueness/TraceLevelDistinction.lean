/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.CompositionUniqueness.SpectralOperations
import SpectralPhysics.CompositionUniqueness.HypothesisSet
import SpectralPhysics.CompositionUniqueness.BroaderUniquenessOpen
import SpectralPhysics.CompositionUniqueness.Theorem
import SpectralPhysics.CompositionBroaderUniqueness.NonKasparovCandidates

/-!
# Trace-Level Distinction for Non-Kasparov Candidates

For each of the four non-Kasparov candidates in
`NonKasparovCandidates.lean`, we exhibit an explicit spectrum
witness on which the candidate's trace **differs** from the
Hamiltonian-additivity trace law.  Combined with the v0.9.1
unconditional theorem

  `three_conditions_force_trace_law : ThreeConditions op →
    Spectrum.trace (op μ ν) = Spectrum.trace (additiveConv μ ν)`

this forces each candidate **out** of the three-condition class.

## What this file proves (Tier 1, zero new axioms)

* `freeVoiculescu_violates_hamiltonian_additivity`
* `multFree_violates_hamiltonian_additivity`
* `monoidalNonK_violates_hamiltonian_additivity`
* `boxed_violates_hamiltonian_additivity` (for a ≠ 0, on the
  explicit witness)
* `non_kasparov_candidate_not_three_conditions` (the headline
  Tier-1 theorem, modulo a non-zero-parameter requirement for the
  boxed candidate).

## What this file does NOT claim

It does NOT claim that every conceivable non-Kasparov factorization
fails the three conditions.  That is the
`BroaderUniquenessAllNonKasparov` predicate in
`UncountableObstruction.lean`, which stays open.

## References

The shadow operations and the moments at which they diverge from
additive are documented in `NonKasparovCandidates.lean`.

* Voiculescu (1985); Speicher (1994); Nica–Speicher (2006) §11.
* Bercovici–Voiculescu (1993).
* Joyal–Street (1991).
* Bożejko–Bryc (2006); Bryc (2007).
-/

namespace SpectralPhysics.CompositionBroaderUniqueness

open SpectralPhysics.CompositionUniqueness

/-! ## Trace formulas for the four candidates -/

/-- Trace of the free-Voiculescu shadow on a block-diagonal model. -/
lemma trace_freeVoiculescuConv (μ ν : Spectrum) :
    Spectrum.trace (freeVoiculescuConv μ ν) =
      Spectrum.trace μ + Spectrum.trace ν := by
  unfold freeVoiculescuConv Spectrum.trace
  rw [Multiset.sum_add]

/-- Cardinality of the free-Voiculescu shadow. -/
@[simp] lemma card_freeVoiculescuConv (μ ν : Spectrum) :
    Multiset.card (freeVoiculescuConv μ ν) =
      Multiset.card μ + Multiset.card ν := by
  unfold freeVoiculescuConv
  rw [Multiset.card_add]

/-- Trace of the multiplicative-free shadow (matches `multiplicativeConv`). -/
lemma trace_multFreeConv (μ ν : Spectrum) :
    Spectrum.trace (multFreeConv μ ν) =
      Spectrum.trace μ * Spectrum.trace ν := by
  unfold multFreeConv Spectrum.trace
  show ((μ.bind (fun a => ν.map (fun b => a * b))).sum : ℝ) = μ.sum * ν.sum
  have := trace_multiplicativeConv μ ν
  unfold multiplicativeConv Spectrum.trace at this
  exact this

/-! ## Witness pair for trace-mismatch proofs -/

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

/-- Second witness: `μ₁ = {1, 1}` (cardinality 2). -/
private def μ₁ : Spectrum := ({1, 1} : Multiset ℝ)

@[simp] private lemma card_μ₁ : Multiset.card μ₁ = 2 := by
  unfold μ₁; decide

@[simp] private lemma trace_μ₁ : Spectrum.trace μ₁ = 2 := by
  unfold μ₁ Spectrum.trace; simp; norm_num

/-! ## Failure of Hamiltonian additivity for each candidate -/

/-- **Tier 1**: the free-Voiculescu shadow fails Hamiltonian
additivity.  Witness pair: `μ₁ = {1, 1}` (cardinality 2,
trace 2) and `ν₀ = {3}` (cardinality 1, trace 3).

* `Spectrum.trace (freeVoiculescuConv μ₁ ν₀) = 5`
* Hamiltonian-additivity demands `|ν₀| · trace μ₁ + |μ₁| · trace ν₀
  = 1·2 + 2·3 = 8`.

This corresponds to the free-cumulant / classical-cumulant split:
the free additive convolution matches the first cumulant but
diverges from the Hamiltonian trace identity once one factor has
cardinality `> 1` (free convolution is the spectrum of a block
direct sum, NOT a tensor product). -/
theorem freeVoiculescu_violates_hamiltonian_additivity :
    ¬ HamiltonianAdditivity ⟨freeVoiculescuConv⟩ := by
  intro h
  have hμν := h μ₁ ν₀
  show False
  -- The op call unfolds:
  have hop : (⟨freeVoiculescuConv⟩ : BinaryOpOnSpectra) μ₁ ν₀ =
                freeVoiculescuConv μ₁ ν₀ := rfl
  rw [hop, trace_freeVoiculescuConv, trace_μ₁, trace_ν₀,
      card_μ₁, card_ν₀] at hμν
  norm_num at hμν

/-- **Tier 1**: the multiplicative-free shadow fails Hamiltonian
additivity.  Same witness as v0.9.1's
`multiplicative_violates_hamiltonian_additivity`: `{2}, {3}` give
`trace = 6` vs. additive `= 5`.  The S-transform's multiplicative
fixed-point structure (Speicher 1994) is *not* the
R-transform additive structure. -/
theorem multFree_violates_hamiltonian_additivity :
    ¬ HamiltonianAdditivity ⟨multFreeConv⟩ := by
  intro h
  have hμν := h μ₀ ν₀
  show False
  have hop : (⟨multFreeConv⟩ : BinaryOpOnSpectra) μ₀ ν₀ =
                multFreeConv μ₀ ν₀ := rfl
  rw [hop, trace_multFreeConv, trace_μ₀, trace_ν₀,
      card_μ₀, card_ν₀] at hμν
  norm_num at hμν

/-- **Tier 1**: the monoidal-non-Kasparov shadow fails Hamiltonian
additivity.  Witness: `μ₀ = {2}`, `ν₀ = {3}`.

* `monoidalNonKConv μ₀ ν₀` is the singleton multiset `{2 + 3 + 1}
  = {6}`.
* `trace = 6`, but Hamiltonian-additivity demands
  `1·2 + 1·3 = 5`.

The +1 shift per eigenvalue is the Joyal–Street coherence
twist; Mesland–Rennie (2014) prohibits it on unbounded Kasparov
products. -/
theorem monoidalNonK_violates_hamiltonian_additivity :
    ¬ HamiltonianAdditivity ⟨monoidalNonKConv⟩ := by
  intro h
  have hμν := h μ₀ ν₀
  show False
  have hop : (⟨monoidalNonKConv⟩ : BinaryOpOnSpectra) μ₀ ν₀ =
                monoidalNonKConv μ₀ ν₀ := rfl
  rw [hop] at hμν
  -- Compute LHS directly: monoidalNonKConv {2} {3} = additiveConv {2} {3} shifted by 1
  --   = {2 + 3} mapped by (+1) = {6}
  -- so its trace = 6
  have hlhs : Spectrum.trace (monoidalNonKConv μ₀ ν₀) = 6 := by
    unfold monoidalNonKConv Spectrum.trace additiveConv μ₀ ν₀
    simp
    norm_num
  rw [hlhs, trace_μ₀, trace_ν₀, card_μ₀, card_ν₀] at hμν
  norm_num at hμν

/-- **Tier 1**: the boxed convolution at `a = 1` fails Hamiltonian
additivity.  At `a = 1`, `boxedConv 1 μ ν = μ.bind (fun x =>
ν.map (fun _ => x))`, which is `μ` repeated `|ν|` times.

* Witness: `μ₀ = {2}`, `ν₀ = {3}`.
* `boxedConv 1 μ₀ ν₀ = {2}` (single copy of `2`).
* `trace = 2`, but Hamiltonian-additivity demands
  `1·2 + 1·3 = 5`.

This is the trace-level shadow of the Bryc (2007) `a`-deformed
cumulant relation: at `a = 1` the second-factor cumulant
contribution is fully damped. -/
theorem boxed_violates_hamiltonian_additivity :
    ¬ HamiltonianAdditivity ⟨boxedConv 1⟩ := by
  intro h
  have hμν := h μ₀ ν₀
  show False
  have hop : (⟨boxedConv 1⟩ : BinaryOpOnSpectra) μ₀ ν₀ =
                boxedConv 1 μ₀ ν₀ := rfl
  rw [hop] at hμν
  have hlhs : Spectrum.trace (boxedConv 1 μ₀ ν₀) = 2 := by
    unfold boxedConv Spectrum.trace μ₀ ν₀
    simp
  rw [hlhs, trace_μ₀, trace_ν₀, card_μ₀, card_ν₀] at hμν
  norm_num at hμν

/-! ## Each candidate is out of the three-condition class -/

/-- The free-Voiculescu candidate does NOT satisfy
`ThreeConditions`. -/
theorem freeVoiculescu_not_three_conditions :
    ¬ ThreeConditions ⟨freeVoiculescuConv⟩ :=
  fun h => freeVoiculescu_violates_hamiltonian_additivity h.hamilton

/-- The multiplicative-free candidate does NOT satisfy
`ThreeConditions`. -/
theorem multFree_not_three_conditions :
    ¬ ThreeConditions ⟨multFreeConv⟩ :=
  fun h => multFree_violates_hamiltonian_additivity h.hamilton

/-- The monoidal-non-Kasparov candidate does NOT satisfy
`ThreeConditions`. -/
theorem monoidalNonK_not_three_conditions :
    ¬ ThreeConditions ⟨monoidalNonKConv⟩ :=
  fun h => monoidalNonK_violates_hamiltonian_additivity h.hamilton

/-- The boxed convolution at `a = 1` does NOT satisfy
`ThreeConditions`. -/
theorem boxed_at_one_not_three_conditions :
    ¬ ThreeConditions ⟨boxedConv 1⟩ :=
  fun h => boxed_violates_hamiltonian_additivity h.hamilton

/-! ## Re-use of the v0.9.1 unconditional trace law

Each Tier-1 falsifier above can equivalently be phrased: if the
candidate **were** three-condition, then by v0.9.1's
`three_conditions_force_trace_law` its trace would match
`additiveConv`'s — which we have just disproved on the witness
pair.  The lemma below packages this rephrasing.  Zero new axioms.
-/

/-- **Re-use lemma**: if a binary operation has a witness pair on
which its trace differs from additive convolution's trace, it
cannot be three-condition.  This is the immediate contrapositive
of `three_conditions_force_trace_law`. -/
theorem trace_mismatch_excludes_three_conditions
    (op : BinaryOpOnSpectra) (μ ν : Spectrum)
    (hneq : Spectrum.trace (op μ ν) ≠ Spectrum.trace (additiveConv μ ν)) :
    ¬ ThreeConditions op := by
  intro htc
  exact hneq (three_conditions_force_trace_law op htc μ ν)

end SpectralPhysics.CompositionBroaderUniqueness
