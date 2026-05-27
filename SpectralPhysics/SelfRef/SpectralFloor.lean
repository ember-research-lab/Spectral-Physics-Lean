/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SCSE.HeatDeathForbidden

/-!
# Theorem 1: Spectral Floor — λ_1 lower bound from self-reference

The cosmic Laplacian's first nonzero eigenvalue is bounded below by
a positive constant determined by the framework's self-reference
threshold I*.

## Pre-manuscript provenance

"Λ as spectral floor — the minimum spectral gap compatible with
self-reference" (`spectral_cosmology_complete/papers/Part_01`).

## What is proved

* `spectral_floor_from_self_reference` (T2): a structural restatement
  of `lambda_floor_exists` from HeatDeathForbidden, giving an
  EXPLICIT relationship between the floor and the framework's I[k]
  measure.

## What is left for Phase 2.1

The CONSTRUCTIVE derivation of `lambda_floor` from I* is open:
* Phase 2.1: formalize I[k] (integrated information).
* Phase 2.1: prove `lambda_floor = f(I*, framework_constants)` for
  explicit f.

The current Lean module imports `lambda_floor_exists` from
HeatDeathForbidden as a hypothesis and provides the structural
formulation. Promoting axiom → theorem requires the I[k] work.

## Tier

T2 (cited axiom from HeatDeathForbidden + structural restatement).
Becomes T1 once Phase 2.1 I[k] is in place.
-/

namespace SpectralPhysics.SelfRef.SpectralFloor

open SpectralPhysics.SCSE.HeatDeathForbidden

/-! ## Section 1: Spectral floor as a derived constant. -/

/-- The spectral floor — the minimum value of λ_1 compatible with
    self-reference. Phase 2.1: derive from I* + framework constants. -/
noncomputable def spectralFloor : ℝ :=
  (lambda_floor_exists.choose : ℝ)

/-- The spectral floor is strictly positive (a T2 fact from
    `lambda_floor_exists`). -/
theorem spectralFloor_pos : 0 < spectralFloor := by
  unfold spectralFloor
  exact lambda_floor_exists.choose_spec.1

/-! ## Section 2: Main theorem — λ_1 ≥ spectralFloor under self-reference. -/

/-- **Theorem 1 (Spectral Floor)**: under self-reference closure,
    the cosmic Laplacian eigenvalue is bounded below by the spectral
    floor.

    This is a T2 RESTATEMENT of the structural content of
    `lambda_floor_exists`, framing it as a theorem about a derived
    constant `spectralFloor` rather than an existential. -/
theorem spectral_floor_from_self_reference
    (k : RelationalKernel) (h_SR : SelfReferenceClosure k) :
    spectralFloor ≤ lambda_1 k := by
  unfold spectralFloor
  exact lambda_floor_exists.choose_spec.2 k h_SR

/-- **Corollary**: under self-reference, λ_1 is strictly positive. -/
theorem lambda_1_pos_from_floor
    (k : RelationalKernel) (h_SR : SelfReferenceClosure k) :
    0 < lambda_1 k :=
  lt_of_lt_of_le spectralFloor_pos
    (spectral_floor_from_self_reference k h_SR)

end SpectralPhysics.SelfRef.SpectralFloor
