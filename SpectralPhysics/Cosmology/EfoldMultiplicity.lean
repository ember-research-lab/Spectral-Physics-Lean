/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# E-fold Multiplicity Reconciliation (Ch 38 / cosmology audit P1)

v0.9 of the manuscript carries **three competing values** of the
inflationary e-fold count `N_e`, quoted in three adjacent sections
without explicit reconciliation.  This file isolates, names, and
distinguishes them as Lean definitions and proves that they are
pairwise distinct natural numbers.  It also fixes the convention that
`N_e = 60` is the value compatible with the CMB scalar-amplitude
closure `A_s ≈ 2.33 × 10⁻⁹` (Theorem `As-closure` in v0.9).

## The three readings (v0.9 line refs)

1. **`Ne_modeActivation = 252`** — v0.9 line 9517,
   Proposition "Two-phase structure" (Phase 2).
   Counts the number of *lighter modes that activate* per σ-roll
   unit during the slow-roll Phase 2: `288 − 36 = 252` (total hidden
   states minus the 36 hidden tops which activate during the violent
   Big Bang Phase 1).  This is a **count of mode activations**, not
   an e-fold count in the metric-expansion sense.

2. **`Ne_treePotential = 45`** — v0.9 line 9767,
   Remark `f4-positives` (iii).
   The number of e-folds that follows from the *tree-level* spectral
   potential, before the topological suppression `S_top` is included.
   This is the **tree-level slow-roll attractor**: a perturbative
   estimate that is replaced by `Ne_AsClosure` once `S_top` is
   included.

3. **`Ne_AsClosure = 60`** — v0.9 line 9704,
   Theorem `As-closure`.
   The value used in `A_s = 2 · Ch₂ · λ_σ · N_e² / π²` to obtain
   `A_s = 2.33 × 10⁻⁹`, matching the Planck 2018 observation
   `A_s^obs = 2.10 × 10⁻⁹` to 11%.  This is the **inflationary
   e-fold count constrained by the CMB**.

## Reconciliation

The three quantities measure **different physical aspects of the same
process** (cf. the user's BOOM reframe on
`compute/friedmann-from-sigmaTr`: "BOOM = slow-roll inflation phase
where high-energy/short-wavelength modes are dense and active; lower
modes progressively activate"):

* `Ne_modeActivation = 252` — counts *spectral activations* (algebraic
  → geometric DOF transitions).  Dimensionally a *count*, not an
  e-fold; the units only coincide if one identifies one e-fold with
  one mode transition, which v0.9 does not assert.
* `Ne_treePotential = 45` — *perturbative e-fold attractor* on the
  tree-level potential `λ_σ = π²/(288τ)`.  Replaced once the
  non-perturbative suppression `λ_σ = exp(−S_top)` is included.
* `Ne_AsClosure = 60` — *non-perturbative inflationary e-fold count*,
  the unique value compatible with the CMB scalar-amplitude
  observation under the `A_s` closure.

The canonical e-fold count for CMB observables is `Ne_AsClosure`.
The other two are quantities that v0.9.1 should explicitly relabel:
mode-activation count and tree-potential attractor, respectively.

## References

* Ben-Shalom, "Spectral Physics", v0.9, §"Mode Activation and the
  Inflationary Clock" (line 9508), §"The Scalar Amplitude $A_s$ via
  $S_{\mathrm{top}}$" (line 9683), Remark `f4-positives` (line 9762).
* `pre_geometric/cosmology_audit/triage.md` — Tier 2 reconciliation
  task.
* `pre_geometric/cosmology_audit/top10.md` — honourable mention #8.
-/

namespace SpectralPhysics.Cosmology

/-! ## Part 1: The three numerical readings -/

/-- **Mode-activation count** (v0.9 line 9517).

Number of lighter (non-hidden-top) modes that activate during the
slow-roll Phase 2 of the algebra-to-geometry transition:
`288 − 36 = 252`, where `288` is the dimension of the hidden sector
and `36` is the number of hidden top-Yukawa modes which activate
during the violent Big Bang (Phase 1).

This is a **count of spectral activations**, not an inflationary
e-fold count in the metric-expansion sense.  v0.9 calls these
"$\sim 252$ e-folds of nearly scale-invariant expansion," but the
identification "one mode activation = one e-fold" is not derived
in v0.9; it is a *naming choice*.  Hence v0.9.1 should relabel this
quantity as the **mode-activation count** to disambiguate from the
CMB-constrained e-fold count `Ne_AsClosure`. -/
def Ne_modeActivation : ℕ := 252

/-- **Tree-potential e-fold attractor** (v0.9 line 9767).

The number of e-folds obtained from the tree-level σ-potential —
i.e. from `λ_σ = π²/(288τ) ≈ 0.124` *without* the topological
suppression `S_top`.  v0.9 Remark `f4-positives` (iii):
"Inflation with $\sim 45$ e-folds follows from the tree-level
potential, consistent with observations."

This is a **perturbative slow-roll attractor**, not the final
e-fold count.  It is superseded by `Ne_AsClosure` once
`λ_σ = exp(−S_top) ≈ 6.3 × 10⁻¹³` is used (Theorem `As-closure`,
v0.9 line 9699). -/
def Ne_treePotential : ℕ := 45

/-- **CMB-compatible inflationary e-fold count** (v0.9 line 9704).

The value used in the scalar-amplitude closure
`A_s = 2 · Ch₂ · λ_σ · N_e² / π²` together with
`λ_σ = exp(−S_top) ≈ 6.3 × 10⁻¹³` and `Ch₂ = 6` to obtain
`A_s = 2.33 × 10⁻⁹`, matching `A_s^obs = 2.10 × 10⁻⁹` to 11%.

This is the **canonical inflationary e-fold count** in v0.9: the one
constrained by the CMB scalar-amplitude observation, and the one
v0.9.1 should retain (relabelling the other two). -/
def Ne_AsClosure : ℕ := 60

/-! ## Part 2: Pairwise distinctness -/

/-- The mode-activation count `252` differs from the tree-potential
attractor `45`. -/
theorem Ne_modeActivation_ne_treePotential :
    Ne_modeActivation ≠ Ne_treePotential := by
  decide

/-- The mode-activation count `252` differs from the CMB-compatible
e-fold count `60`. -/
theorem Ne_modeActivation_ne_AsClosure :
    Ne_modeActivation ≠ Ne_AsClosure := by
  decide

/-- The tree-potential attractor `45` differs from the CMB-compatible
e-fold count `60`. -/
theorem Ne_treePotential_ne_AsClosure :
    Ne_treePotential ≠ Ne_AsClosure := by
  decide

/-- **Pairwise distinctness** (the conjunction).

The three v0.9 readings of "N_e" are three different natural numbers:
`252`, `45`, and `60`.  They cannot all be the same physical
quantity. -/
theorem Ne_definitions_distinct :
    Ne_modeActivation ≠ Ne_treePotential ∧
    Ne_modeActivation ≠ Ne_AsClosure ∧
    Ne_treePotential ≠ Ne_AsClosure :=
  ⟨Ne_modeActivation_ne_treePotential,
   Ne_modeActivation_ne_AsClosure,
   Ne_treePotential_ne_AsClosure⟩

/-! ## Part 3: The CMB-compatible value -/

/-- **CMB compatibility**: `Ne_AsClosure = 60`.

Trivial unfolding lemma; isolated as a theorem to make the
canonical-value identification explicit at the type-theoretic level. -/
theorem Ne_CMB_compatible : Ne_AsClosure = 60 := rfl

/-! ## Part 4: Observational compatibility predicate

We expose the empirical claim that *only* `Ne = 60` is compatible
with the CMB `A_s` observation (the v0.9 closure value).  This is an
**axiom-class** statement: it is the empirical content of v0.9
Theorem `As-closure`, not a Lean proof.
-/

/-- The set of e-fold counts compatible with the CMB scalar-amplitude
observation, as used in v0.9 Theorem `As-closure`.

In v0.9 this set is `{60}` (a single value, modulo 11% closure
tolerance).  We model it as a decidable predicate on `ℕ` — the
predicate that says "this number is the v0.9 `A_s`-closure value". -/
def is_observationally_compatible (n : ℕ) : Bool := decide (n = 60)

/-- **`Ne_AsClosure` is observationally compatible** (with the v0.9
`A_s`-closure convention).

This is `rfl` once one notes `decide (60 = 60) = true`. -/
theorem Ne_canonical_for_CMB :
    is_observationally_compatible Ne_AsClosure = true := by
  unfold is_observationally_compatible Ne_AsClosure
  decide

/-- **The other two readings are *not* observationally compatible**
(under the same convention).

This is the operational content of "the three readings measure
different physical quantities": only one is the inflationary e-fold
count constrained by CMB. -/
theorem Ne_others_not_CMB_compatible :
    is_observationally_compatible Ne_modeActivation = false ∧
    is_observationally_compatible Ne_treePotential = false := by
  refine ⟨?_, ?_⟩
  · unfold is_observationally_compatible Ne_modeActivation
    decide
  · unfold is_observationally_compatible Ne_treePotential
    decide

/-! ## Part 5: Structural decomposition of the mode-activation count

The mode-activation reading `Ne_modeActivation = 252` decomposes
algebraically as `288 − 36`.  We expose this so v0.9.1 can relabel
the quantity transparently.
-/

/-- Hidden-sector dimension (cf. `Cosmology.Predictions.darkDim`). -/
def hiddenSectorDim : ℕ := 288

/-- Number of hidden top-Yukawa modes activating during Phase 1
(the violent Big Bang). -/
def hiddenTopModes : ℕ := 36

/-- **Phase 2 / mode-activation decomposition**:
`Ne_modeActivation = hiddenSectorDim − hiddenTopModes`. -/
theorem Ne_modeActivation_decomp :
    Ne_modeActivation = hiddenSectorDim - hiddenTopModes := by
  decide

/-! ## Part 6: Reconciliation summary

The three readings are three *physical observables*, only one of
which is constrained by the CMB scalar-amplitude observation.

* `Ne_modeActivation` — count of slow-roll mode activations
  (Phase 2 of the BOOM, hidden-light-sector roll).
* `Ne_treePotential` — tree-level slow-roll e-fold attractor
  (perturbative estimate, superseded once `S_top` is included).
* `Ne_AsClosure` — CMB-compatible non-perturbative e-fold count
  (the canonical "N_e" for v0.9.1).

The reconciliation theorem below is the single statement that
captures all of this: the three readings are pairwise distinct, only
the third is observationally compatible, and the first decomposes
algebraically into 288 − 36. -/

/-- **Reconciliation theorem**.

Bundle the three statements that v0.9.1 should attach to its
disambiguation table:

(i)  the three readings are pairwise distinct;
(ii) only `Ne_AsClosure = 60` is CMB-compatible (under the v0.9
     closure convention);
(iii)`Ne_modeActivation` decomposes as `hiddenSectorDim −
     hiddenTopModes`. -/
theorem Ne_reconciliation :
    (Ne_modeActivation ≠ Ne_treePotential ∧
     Ne_modeActivation ≠ Ne_AsClosure ∧
     Ne_treePotential ≠ Ne_AsClosure) ∧
    (is_observationally_compatible Ne_AsClosure = true) ∧
    (is_observationally_compatible Ne_modeActivation = false ∧
     is_observationally_compatible Ne_treePotential = false) ∧
    (Ne_modeActivation = hiddenSectorDim - hiddenTopModes) :=
  ⟨Ne_definitions_distinct,
   Ne_canonical_for_CMB,
   Ne_others_not_CMB_compatible,
   Ne_modeActivation_decomp⟩

end SpectralPhysics.Cosmology
