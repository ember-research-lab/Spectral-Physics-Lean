/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Matrix

/-!
# The Void Dichotomy — `HeatDeathForbidden` split into theorems

Formalizes Parts A and B of the void-dichotomy insert
(`void-dichotomy-insert.tex`, session 2026-07-04/05; spec
`heatdeath-axiom-upgrade.tex`): the content of the previously asserted
axiom block around `SCSE.HeatDeathForbidden.I_star` is split into

* **Part A (dynamical no-annihilation, T1)** — `thm_no_annihilation_i`:
  the heat operator `exp (-(τ • L))` is a unit for every finite `τ`
  (no self-adjointness needed; stated on top for self-adjoint `L`);
  `thm_no_annihilation_ii`: the normalized heat weights converge, as
  `τ → ∞`, to the ground indicator normalized by the ground
  multiplicity, which is `≥ 1` (`one_le_groundMult`,
  `one_le_groundProjector_rank`). Heat death as asymptotic
  ground-dominance is *permitted*; annihilation is *forbidden*.

* **Part B (static small-solution exclusion, T1)** —
  `prop_small_exclusion`: the ignition datum is a *partial* function
  (`Option`), literally undefined (`none`) whenever there are at most
  one spectral level — the ignition clause of the self-reference
  condition fails at the *existence* step, not vacuously. This closes
  the vacuity loophole of the insert's Open Problem syntactically.

* **Part B (dichotomy, T2 conditional)** — `prop_dichotomy`: citing the
  manuscript's forcing chain as a hypothesis (Cayley–Dickson
  termination, 3×128 mode count, gauge/chirality closures — cited, not
  re-proved), the solution set is contained in `{void, k*}`.

* **Part C (located meta-residue)** lives in `HeatDeathForbidden.lean`
  as the single documented permanent assumption
  `instantiation_nonempty` — see there, and the ledger in
  `SpectralPhysics/SCSE/STATUS.md`.

The old axiom's *name* survives as a theorem here:
`heat_death_forbidden` — heat death forbidden *as annihilation*,
permitted *as asymptotics*.

## Tier / status

* Part A (i): **CLOSED** (T1) — `Matrix.isUnit_exp`
  (`exp A * exp (-A) = 1` via `Matrix.exp_add_of_commute`; `A` and
  `-A` commute), no self-adjointness required.
* Part A (ii): **CLOSED in the diagonalized basis** (T1) — the limit is
  proved for the eigenvalue weights `heatWeight` and packaged as a
  matrix limit for diagonal Laplacians
  (`normalized_heat_tendsto_groundProjector`). The conjugation of this
  limit through the eigenbasis of a general self-adjoint `L`
  (`Matrix.IsHermitian.spectral_theorem`) is NOT formalized — that
  bridge is the named CONDITIONAL gap; see STATUS.md.
* Part B exclusion: **CLOSED** (T1). Dichotomy: **CONDITIONAL** (T2) on
  the forcing chain, taken as a hypothesis by design ("cite, do not
  re-prove").

`#print axioms` is emitted at compile time for the main results at the
bottom of this file: no axioms beyond `propext`, `Classical.choice`,
`Quot.sound`.
-/

open Filter Topology

-- Same workaround Mathlib's own `MatrixExponential.lean` uses for `exp`
-- on matrices (lean4#10414): the `TopologicalSpace (Matrix n n ℝ)`
-- instances only unify with transparency-respecting defeq disabled.
set_option backward.isDefEq.respectTransparency false

namespace SpectralPhysics.SCSE.VoidDichotomy

open NormedSpace -- for `exp`

/-! ## Part A (i) — the heat operator is a unit at every finite τ.

No self-adjointness is needed: `τ • L` and `-(τ • L)` commute, so
`exp (τ • L) * exp (-(τ • L)) = exp 0 = 1`. -/

section HeatUnit

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The two heat factors multiply to the identity: the flow damps modes
and annihilates none. (`Matrix.exp_add_of_commute` on the commuting pair
`τ • L`, `-(τ • L)`.) -/
theorem heat_exp_mul_exp_neg (L : Matrix n n ℝ) (τ : ℝ) :
    exp (τ • L) * exp (-(τ • L)) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl (τ • L)).neg_right,
    add_neg_cancel, exp_zero]

/-- **Part A (i), general form (T1)**: the heat operator `exp (-(τ • L))`
is a unit for every finite `τ` — for *any* square real matrix `L`,
self-adjoint or not. -/
theorem heat_isUnit (L : Matrix n n ℝ) (τ : ℝ) :
    IsUnit (exp (-(τ • L))) :=
  Matrix.isUnit_exp _

/-- **Theorem `thm_no_annihilation` part (i) (T1)** — the self-adjoint
version asked for by the spec, an instance of `heat_isUnit`: for a
self-adjoint (Hermitian, here real symmetric) Laplacian `L` of a nonempty
configuration, the heat operator is invertible at every finite `τ`.
The mode count is a flow invariant; annihilation would require a
non-invertible jump the semigroup cannot produce. -/
theorem thm_no_annihilation_i {L : Matrix n n ℝ} (_hL : L.IsHermitian)
    (τ : ℝ) : IsUnit (exp (-(τ • L))) :=
  heat_isUnit L τ

end HeatUnit

/-! ## Part A (ii) — normalized heat weights → ground projector.

Diagonalized basis: the Laplacian is presented by its eigenvalue
function `μ : n → ℝ` on a nonempty finite index type. The normalized
heat weight of mode `k` at flow parameter `τ` is
`exp (-(τ μ_k)) / ∑_j exp (-(τ μ_j))`; as `τ → ∞` it converges to the
normalized indicator of the ground level set, whose cardinality (the
ground multiplicity, = rank of the ground projector) is at least 1. -/

section Diagonalized

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The ground level: the lowest eigenvalue. Exists for any nonempty
finite spectrum — "a lowest eigenvalue with at least one eigenvector
exists for any self-adjoint operator on `𝓗 ≠ {0}`". -/
noncomputable def groundLevel (μ : n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty μ

omit [DecidableEq n] in
theorem groundLevel_le (μ : n → ℝ) (k : n) : groundLevel μ ≤ μ k :=
  Finset.inf'_le _ (Finset.mem_univ k)

/-- The ground level set: modes at the lowest eigenvalue. -/
noncomputable def groundSet (μ : n → ℝ) : Finset n :=
  @Finset.filter _ (fun k => μ k = groundLevel μ) (Classical.decPred _)
    Finset.univ

omit [DecidableEq n] in
theorem mem_groundSet {μ : n → ℝ} {k : n} :
    k ∈ groundSet μ ↔ μ k = groundLevel μ := by
  simp [groundSet]

/-- The ground multiplicity (= rank of the ground projector). -/
noncomputable def groundMult (μ : n → ℝ) : ℕ :=
  (groundSet μ).card

omit [DecidableEq n] in
/-- The ground level is attained: the ground set is nonempty, so the
ground multiplicity — the rank of the ground projector — is `≥ 1`. -/
theorem one_le_groundMult (μ : n → ℝ) : 1 ≤ groundMult μ := by
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_mem_eq_inf' (H := Finset.univ_nonempty) μ
  exact Finset.card_pos.mpr ⟨k, mem_groundSet.mpr hk.symm⟩

omit [DecidableEq n] in
theorem groundMult_ne_zero (μ : n → ℝ) : (groundMult μ : ℝ) ≠ 0 := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mp (one_le_groundMult μ)

/-- The normalized heat weight of mode `k` at flow parameter `τ`
(diagonal entry of `exp (-(τ L)) / Tr exp (-(τ L))` in the eigenbasis). -/
noncomputable def heatWeight (μ : n → ℝ) (τ : ℝ) (k : n) : ℝ :=
  Real.exp (-(τ * μ k)) / ∑ j, Real.exp (-(τ * μ j))

omit [DecidableEq n] in
/-- Gauge freedom: the weights are invariant under shifting the spectrum
by the ground level (multiply numerator and denominator by
`exp (τ · groundLevel)`). -/
theorem heatWeight_eq_shifted (μ : n → ℝ) (τ : ℝ) (k : n) :
    heatWeight μ τ k =
      Real.exp (-(τ * (μ k - groundLevel μ))) /
        ∑ j, Real.exp (-(τ * (μ j - groundLevel μ))) := by
  have hshift : ∀ j : n,
      Real.exp (-(τ * (μ j - groundLevel μ))) =
        Real.exp (-(τ * μ j)) * Real.exp (τ * groundLevel μ) := by
    intro j
    rw [← Real.exp_add]
    ring_nf
  simp only [hshift, ← Finset.sum_mul, heatWeight]
  rw [mul_div_mul_right _ _ (Real.exp_ne_zero _)]

/-- `exp (-(τ d)) → 0` as `τ → ∞` for `d > 0`: excited modes lose all
normalized weight. -/
theorem tendsto_exp_neg_mul_atTop {d : ℝ} (hd : 0 < d) :
    Tendsto (fun τ : ℝ => Real.exp (-(τ * d))) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Tendsto.atTop_mul_const hd tendsto_id)

/-- Each shifted factor converges to the ground indicator. -/
theorem tendsto_shifted_factor (μ : n → ℝ) (j : n) :
    Tendsto (fun τ : ℝ => Real.exp (-(τ * (μ j - groundLevel μ)))) atTop
      (𝓝 (if j ∈ groundSet μ then 1 else 0)) := by
  by_cases hj : j ∈ groundSet μ
  · rw [if_pos hj]
    have h0 : μ j - groundLevel μ = 0 :=
      sub_eq_zero.mpr (mem_groundSet.mp hj)
    simp only [h0, mul_zero, neg_zero, Real.exp_zero]
    exact tendsto_const_nhds
  · rw [if_neg hj]
    exact tendsto_exp_neg_mul_atTop
      (sub_pos.mpr (lt_of_le_of_ne (groundLevel_le μ j)
        (fun h => hj (mem_groundSet.mpr h.symm))))

/-- The shifted partition function converges to the ground multiplicity. -/
theorem tendsto_shifted_partition (μ : n → ℝ) :
    Tendsto (fun τ : ℝ => ∑ j, Real.exp (-(τ * (μ j - groundLevel μ))))
      atTop (𝓝 (groundMult μ : ℝ)) := by
  have hsum :
      (∑ j, if j ∈ groundSet μ then (1 : ℝ) else 0) = (groundMult μ : ℝ) := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul, mul_one, groundMult]
  rw [← hsum]
  exact tendsto_finset_sum _ fun j _ => tendsto_shifted_factor μ j

/-- **Theorem `thm_no_annihilation` part (ii), diagonalized basis (T1)**:
the normalized heat weight of every mode converges, as `τ → ∞`, to the
ground indicator normalized by the ground multiplicity. Together with
`one_le_groundMult` this is "the normalized forward-infinity limit is
the ground projection, of rank `≥ 1`": running the flow to infinity
manufactures the ground projector, and `Ran P₀ ≠ {0}` — heat death as
ground-dominance is permitted, annihilation is not. -/
theorem thm_no_annihilation_ii (μ : n → ℝ) (k : n) :
    Tendsto (fun τ : ℝ => heatWeight μ τ k) atTop
      (𝓝 ((if k ∈ groundSet μ then 1 else 0) / groundMult μ)) := by
  simp only [heatWeight_eq_shifted]
  exact (tendsto_shifted_factor μ k).div (tendsto_shifted_partition μ)
    (groundMult_ne_zero μ)

/-! ### Matrix packaging (diagonal Laplacian)

The same limit stated for the actual normalized heat *operator*
`exp (-(τ L)) / Tr exp (-(τ L))` when `L = diagonal μ` — i.e. in the
basis in which the self-adjoint Laplacian has been diagonalized. -/

/-- The ground projector `P₀` (in the diagonalized basis): diagonal
indicator of the ground level set. -/
noncomputable def groundProjector (μ : n → ℝ) : Matrix n n ℝ :=
  Matrix.diagonal fun k => if k ∈ groundSet μ then (1 : ℝ) else 0

/-- `P₀` is idempotent — a genuine projector. -/
theorem groundProjector_mul_self (μ : n → ℝ) :
    groundProjector μ * groundProjector μ = groundProjector μ := by
  rw [groundProjector, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases hk : k ∈ groundSet μ <;> simp [hk]

/-- The rank of the ground projector is the ground multiplicity. -/
theorem groundProjector_rank (μ : n → ℝ) :
    (groundProjector μ).rank = groundMult μ := by
  classical
  rw [groundProjector, Matrix.rank_diagonal, groundMult]
  rw [Fintype.card_subtype]
  congr 1
  ext k
  by_cases hk : k ∈ groundSet μ <;> simp [hk]

/-- `rk P₀ ≥ 1`: the ground projection is nonzero — the ground state is
a state. -/
theorem one_le_groundProjector_rank (μ : n → ℝ) :
    1 ≤ (groundProjector μ).rank := by
  rw [groundProjector_rank]; exact one_le_groundMult μ

omit [Nonempty n] in
/-- The heat operator of a diagonal Laplacian is the diagonal of the
scalar heat factors. -/
theorem exp_neg_smul_diagonal (μ : n → ℝ) (τ : ℝ) :
    exp (-(τ • Matrix.diagonal μ)) =
      Matrix.diagonal fun j => Real.exp (-(τ * μ j)) := by
  rw [← Matrix.diagonal_smul, Matrix.diagonal_neg, Matrix.exp_diagonal]
  congr 1
  funext j
  rw [Pi.exp_def, Real.exp_eq_exp_ℝ]
  simp [smul_eq_mul]

omit [Nonempty n] in
/-- Trace of the heat operator = partition function. -/
theorem trace_exp_neg_smul_diagonal (μ : n → ℝ) (τ : ℝ) :
    (exp (-(τ • Matrix.diagonal μ))).trace =
      ∑ j, Real.exp (-(τ * μ j)) := by
  rw [exp_neg_smul_diagonal, Matrix.trace_diagonal]

/-- **Part A (ii), matrix form for diagonal Laplacians (T1)**: the
normalized heat operator converges entrywise to the normalized ground
projector, `exp (-(τ L)) / Tr exp (-(τ L)) → P₀ / rk P₀` as `τ → ∞`.

CONDITIONAL gap (named; see STATUS.md): this is the statement *in the
diagonalized basis*. Conjugating it through the eigenbasis of a general
self-adjoint `L` (`Matrix.IsHermitian.spectral_theorem`) is not
formalized here. -/
theorem normalized_heat_tendsto_groundProjector (μ : n → ℝ) (i j : n) :
    Tendsto
      (fun τ : ℝ =>
        ((exp (-(τ • Matrix.diagonal μ))).trace)⁻¹ *
          exp (-(τ • Matrix.diagonal μ)) i j)
      atTop
      (𝓝 (((groundProjector μ).rank : ℝ)⁻¹ * groundProjector μ i j)) := by
  simp only [exp_neg_smul_diagonal, Matrix.trace_diagonal,
    groundProjector_rank]
  by_cases hij : i = j
  · subst hij
    have h := thm_no_annihilation_ii μ i
    simp only [heatWeight, div_eq_inv_mul] at h
    simpa [Matrix.diagonal_apply_eq, groundProjector,
      div_eq_inv_mul] using h
  · simp only [Matrix.diagonal_apply_ne _ hij, groundProjector, mul_zero]
    exact tendsto_const_nhds

/-! ## The old axiom's name, kept as a theorem

"Heat death forbidden *as annihilation*, permitted *as asymptotics*":
at every finite `τ` the heat operator is a unit (no mode is
annihilated; the mode count is flow-invariant), and the `τ → ∞`
normalized limit is the ground projector of rank `≥ 1` — relaxation
toward a genuine nonzero state, never toward the void. -/

/-- **Corollary (old name; T1)** — heat death forbidden as annihilation
(every finite-`τ` heat operator is a unit), permitted as asymptotics
(the flow relaxes toward the ground projector, a nonzero state:
`rk P₀ ≥ 1`). -/
theorem heat_death_forbidden (μ : n → ℝ) :
    (∀ τ : ℝ, IsUnit (exp (-(τ • Matrix.diagonal μ)))) ∧
      1 ≤ (groundProjector μ).rank :=
  ⟨fun τ => heat_isUnit _ τ, one_le_groundProjector_rank μ⟩

end Diagonalized

/-! ## Part B — the ignition datum is a partial function

The ignition functional is defined as a ratio of *distinct* spectral
levels. We formalize the datum it needs — a pair of distinct levels,
canonically (min, max) — as a *partial* function on the finite set of
spectral levels: `none` unless at least two distinct levels exist. At
`N ≤ 1` the self-reference condition's ignition clause therefore fails
at the *existence* step: the quantity the axiom quantifies over is not
defined. Not vacuously true, not vacuously false — undefined. This
closes the insert's Open Problem ("non-vacuous ignition at the
definition level") syntactically. -/

/-- The ignition datum on a finite set of spectral levels: the extreme
pair of distinct levels, *iff* at least two distinct levels exist.
A partial function — `Option`, not a default value. -/
def ignitionDatum {α : Type*} [LinearOrder α] (s : Finset α) :
    Option (α × α) :=
  if h : 1 < s.card then
    some (s.min' (Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.one_pos h.le)),
      s.max' (Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.one_pos h.le)))
  else none

/-- The ignition datum exists iff there are at least two distinct
spectral levels. -/
theorem ignitionDatum_isSome_iff {α : Type*} [LinearOrder α]
    (s : Finset α) : (ignitionDatum s).isSome ↔ 1 < s.card := by
  by_cases h : 1 < s.card <;> simp [ignitionDatum, h]

/-- **Proposition `prop_small_exclusion` (T1)**: at most one spectral
level ⇒ the ignition datum does not exist. The smallest candidate fixed
points fail the self-reference clause *non-vacuously*: the ignition
functional is undefined, so the ignition clause fails at the existence
step. -/
theorem prop_small_exclusion {α : Type*} [LinearOrder α] (s : Finset α)
    (h : s.card ≤ 1) : ignitionDatum s = none :=
  dif_neg (by omega)

/-- Dimension-indexed form: a configuration on `Fin N` with `N ≤ 1` has
at most one spectral level, so its ignition datum is `none`. Covers
both the void (`N = 0`: no trace to feed back) and the point (`N = 1`:
spectrum `{0}`, no self/other distinction). -/
theorem prop_small_exclusion_dim {N : ℕ} (hN : N ≤ 1) (μ : Fin N → ℝ) :
    ignitionDatum (Finset.univ.image μ) = none :=
  prop_small_exclusion _
    (le_trans (Finset.card_image_le.trans (by simp)) hN)

/-! ### Executable checks (Part B: N = 0, 1, 2; Part A: 3-mode example) -/

-- N = 0 (the void): no levels, no ignition datum.
example : ignitionDatum (∅ : Finset ℚ) = none := by decide

-- N = 1 (the point): spectrum {0}, no ignition datum.
example : ignitionDatum ({0} : Finset ℚ) = none := by decide

-- N = 2 (two-level toy spectrum {0, 3}): the ignition datum exists…
example : (ignitionDatum ({0, 3} : Finset ℚ)).isSome := by decide

-- …and is the distinct pair (0, 3).
example : ignitionDatum ({0, 3} : Finset ℚ) = some (0, 3) := by decide

-- ℝ-typed 2-level toy (the triad's {0, δ} shape, δ = 3 here).
example : (ignitionDatum ({0, 3} : Finset ℝ)).isSome := by
  rw [ignitionDatum_isSome_iff]
  rw [Finset.card_insert_of_notMem (by norm_num), Finset.card_singleton]
  norm_num

-- Part A executable check, 3-mode example: triangle-graph Laplacian
-- eigenvalues (0, 3, 3) — ground multiplicity 1 (the constant mode),
-- computed decidably over ℚ.
example :
    (Finset.univ.filter fun k => (![0, 3, 3] : Fin 3 → ℚ) k = 0).card
      = 1 := by decide

-- Part A (i) on the concrete 3-mode Laplacian: the heat operator of the
-- triangle graph is a unit at every finite τ (instance of
-- `thm_no_annihilation_i`; the matrix is real symmetric).
example (τ : ℝ) :
    IsUnit (exp (-(τ • (!![2, -1, -1; -1, 2, -1; -1, -1, 2] :
      Matrix (Fin 3) (Fin 3) ℝ)))) :=
  heat_isUnit _ τ

/-! ## Part B — the conditional dichotomy

`Sol(SCSE) ⊆ {∅, k*}` — the void and the world, nothing between.
Conditional (T2) on the manuscript's forcing chain (Cayley–Dickson
termination at 𝕆 by Hurwitz; the 3×128 = 384 mode count; gauge and
chirality closures), **cited as a hypothesis, not re-proved** — per the
insert's Lean-upgrade section. `prop_small_exclusion` supplies the
non-vacuous failure of every small candidate; the forcing chain pushes
any ignitable solution to the full lock. -/

/-- **Proposition `prop_dichotomy` (T2 — conditional)**: given
(1) every nonvoid solution has a defined ignition datum (Part B
exclusion applied through the self-reference condition), and
(2) the manuscript's forcing chain — every solution whose ignition
datum exists is the full lock `k*` — the solution set is contained in
`{void, k*}`. Theorem `thm_no_annihilation` adds that the two branches
are dynamically disconnected. -/
theorem prop_dichotomy {α : Type*} (Sol : Set α) (void kstar : α)
    (spectrumOf : α → Finset ℝ)
    (h_ignition : ∀ s ∈ Sol, s ≠ void →
      (ignitionDatum (spectrumOf s)).isSome)
    (h_forcing : ∀ s ∈ Sol, (ignitionDatum (spectrumOf s)).isSome →
      s = kstar) :
    Sol ⊆ ({void, kstar} : Set α) := by
  intro s hs
  by_cases hv : s = void
  · exact Or.inl hv
  · exact Or.inr (h_forcing s hs (h_ignition s hs hv))

/-! ## Axiom audit (emitted at compile time) -/

#print axioms thm_no_annihilation_i
#print axioms thm_no_annihilation_ii
#print axioms normalized_heat_tendsto_groundProjector
#print axioms one_le_groundProjector_rank
#print axioms heat_death_forbidden
#print axioms prop_small_exclusion
#print axioms prop_small_exclusion_dim
#print axioms prop_dichotomy

end SpectralPhysics.SCSE.VoidDichotomy
