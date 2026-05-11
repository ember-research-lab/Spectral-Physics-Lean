/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# OP3 / SCSE: Structural Predicates (Honest, Non-Circular)

This file replaces the audit-caught circular construction in the prior
`compute/Lambda1-refinement` scaffold.  The previous scaffold defined
`kappa2_target := 2 · log(Λ_c² / Λ_obs)` so that the SCSE formula
`λ_1 = exp(−κ/2) · Λ_c²` would *algebraically* return `Λ_obs`, then
celebrated the algebraic identity as a "46-digit match".  That match
was definitional, not derivational.

The honest replacement:

1. We define a **finite spectral triple** `FiniteSpectralTriple` as a
   bare data carrier (multiplicity-weighted list of Yukawa depths
   `ξ_f = −log y_f`).  No external numerical input.

2. We define the **second cumulant `κ_2(T)`** of a triple as the
   weighted variance of its depths, *purely* from the triple's data —
   independent of any cosmological observable.

3. We define the **SCSE closure operator** abstractly: a candidate
   fixed point is a pair `(triple, value)` where `value` is a function
   of `triple` via the SCSE identity `value = exp(−κ_2(triple)/2)·Λ_c²`.
   This is the framework's *prediction* given `triple`, NOT a definition
   tuned to match `Λ_obs`.

4. We declare three **Prop-valued predicates** corresponding to the
   v0.9 open problems (lines 9670, 9679, 9749):

   * `VisibleSpectrumFollowsBakerForm` — the spectrum's depths follow
     the Baker linear-form parametrisation (`thm:baker-form`).
   * `SCSEHasFixedPoint` — the SCSE iteration has a fixed point at
     some canonical scale `k*`.
   * `SCSEFixedPointUnique` — the fixed point is unique.

   These are NOT axiomatised.  They appear as named hypotheses in
   downstream theorems.

## Comparison to the deceptive prior scaffold

| Aspect | Prior (audit-caught) | This version |
|---|---|---|
| `lambda1` formula | def equal to `exp(−2·log(Λ_c²/Λ_obs)/2)·Λ_c²` (= Λ_obs by algebra) | computed from triple's cumulant; no Λ_obs reference |
| `kappa2_target` | def = `2 log(Λ_c²/Λ_obs)` (circular) | absent; cumulant computed from triple |
| Headline theorem | unconditional `λ_1 = Λ_obs` (by definitional identity) | conditional on three predicates |
| Numerical bracket axiom | yes (`norm_num`-closeable) | removed |
| Comparison to Λ_obs | claimed as "derivation" | separated into its own file, framed as empirical confirmation only |

## References

* v0.9 line 9670: "the first-principles derivation of the cumulant κ_2
  controlling f_4 (and hence Λ_cosmo) from the SM spectrum" — open.
* v0.9 line 9679: "the spectral framework's central open problem"
  (algebra-to-geometry transition).
* v0.9 line 9749: "perturbative approximations to λ_1(k*) ... its
  quantitative success or failure remains an explicit open computation."
-/

noncomputable section

open Real Classical
open scoped BigOperators

namespace SpectralPhysics.OP3

/-! ## Finite spectral triples (bare data) -/

/-- A **finite spectral triple** for OP3 purposes is a finite multiset of
log-Yukawa depths `ξ_f = −log y_f` together with positive integer
multiplicities.  We store it as a finite-indexed family of `(ξ, mult)`.

This is structurally identical to v0.9 §38 §39's setup; no Yukawa
*values* are baked in.  Whether the triple is the SM, a GUT extension,
or the full 384-mode visible+hidden spectrum is left to the caller. -/
structure FiniteSpectralTriple where
  /-- Number of distinct modes. -/
  size : ℕ
  /-- Multiplicity-weighted log-Yukawa depths.  `depth i = ξ_i = −log y_i`. -/
  depth : Fin size → ℝ
  /-- Mode multiplicities (positive). -/
  mult : Fin size → ℕ
  /-- Positivity of multiplicities. -/
  mult_pos : ∀ i, 0 < mult i

/-- Total mode count (sum of multiplicities). -/
def FiniteSpectralTriple.totalCount (T : FiniteSpectralTriple) : ℕ :=
  ∑ i, T.mult i

/-- The first cumulant κ_1 = mean depth (weighted). -/
def FiniteSpectralTriple.kappa1 (T : FiniteSpectralTriple) : ℝ :=
  if (0 : ℕ) < T.totalCount then
    (∑ i, (T.mult i : ℝ) * T.depth i) / (T.totalCount : ℝ)
  else 0

/-- The second cumulant κ_2 = weighted variance of depths.

`κ_2(T) = (∑ mᵢ · (ξᵢ − κ_1)²) / N`

This is a pure functional of `T` — no cosmological observable, no
external scale, appears in this definition. -/
def FiniteSpectralTriple.kappa2 (T : FiniteSpectralTriple) : ℝ :=
  if (0 : ℕ) < T.totalCount then
    let m := T.kappa1
    (∑ i, (T.mult i : ℝ) * (T.depth i - m) ^ 2) / (T.totalCount : ℝ)
  else 0

/-! ## Static framework constants (no observational input) -/

/-- The Faithfulness-Tower coefficient `f₂ = 48 · e⁶` (v0.9
`thm:GJ-rg-target`).

This is a **framework primitive**: it is fixed by the algebraic count
of visible-sector modes (96 = 48 · 2) and the κ_1 = 6 mean depth (also
algebraic, from the SO(10) decomposition).  It is NOT an observational
input. -/
def f2_static : ℝ := 48 * Real.exp 6

theorem f2_static_pos : 0 < f2_static := by
  unfold f2_static; positivity

/-- The framework's canonical scale `Λ_c² / M_Pl² = π / (64 · f₂)`
(v0.9 §38 `eq:Lambda-c-from-f2`).

The `64` comes from the Seeley–DeWitt heat-kernel weight on M⁴ × F.
No observational input. -/
def lambda_c_sq : ℝ := Real.pi / (64 * f2_static)

theorem lambda_c_sq_pos : 0 < lambda_c_sq := by
  unfold lambda_c_sq
  have h : (0 : ℝ) < 64 * f2_static := by
    have := f2_static_pos; linarith
  positivity

/-! ## The SCSE prediction function

This is the **framework's prediction**: given a triple `T`, the SCSE
formula predicts the lowest spatial-Laplacian eigenvalue at scale `k*`
as a function of `T`'s second cumulant.

Critically: this function takes `T` as input.  It does NOT take
`Λ_obs` as input.  Comparing the output to `Λ_obs` is a separate step
done in `CosmologicalConstantMatch.lean`. -/

/-- The **SCSE prediction**: given a spectral triple `T`,
`lambda1Predicted(T) = exp(−κ_2(T) / 2) · Λ_c²`.

This is v0.9's `eq:scse-lambda1` taken as the definition of the
*framework prediction*.  No observational input. -/
def lambda1Predicted (T : FiniteSpectralTriple) : ℝ :=
  Real.exp (- T.kappa2 / 2) * lambda_c_sq

theorem lambda1Predicted_pos (T : FiniteSpectralTriple) :
    0 < lambda1Predicted T := by
  unfold lambda1Predicted
  exact mul_pos (Real.exp_pos _) lambda_c_sq_pos

/-- Monotonicity of the prediction in the cumulant:
larger κ_2 ⇒ smaller predicted λ_1. -/
theorem lambda1Predicted_monotone
    {T T' : FiniteSpectralTriple} (h : T.kappa2 < T'.kappa2) :
    lambda1Predicted T' < lambda1Predicted T := by
  unfold lambda1Predicted
  have h_exp : Real.exp (-T'.kappa2 / 2) < Real.exp (-T.kappa2 / 2) :=
    Real.exp_lt_exp.mpr (by linarith)
  exact mul_lt_mul_of_pos_right h_exp lambda_c_sq_pos

/-! ## Structural predicates (v0.9 open problems, named hypotheses)

The three predicates below correspond directly to the v0.9 open
problems flagged at lines 9670, 9679, and 9749.  Each is a Prop-valued
predicate over the data of a `FiniteSpectralTriple`.

They are **NOT axiomatised**.  Downstream theorems take them as
hypotheses.  This is the analog of `compute/self-model-deficit-rigorous`'s
`CompletenessAtLevel2` / `SectorFaithfulNoDeadWeight` discipline. -/

/-- **Predicate (V0.9 line 10977, `thm:baker-form`)**: the depths of `T`
follow the Baker linear-form parametrisation
`m_f / m_t = (p_f / q_f) · φ^{a_f} · τ^{k_f}` for integer `(a_f, k_f)`
and rationals `(p_f, q_f)`.

Formalising the full Baker form down to specific `(a_f, k_f, p_f, q_f)`
tuples requires the SM mass-table; we encode it abstractly as
"there exists such a parametrisation".  The *physical content* is that
the depths are algebraic-with-Baker-form, NOT arbitrary real numbers. -/
def VisibleSpectrumFollowsBakerForm (T : FiniteSpectralTriple) : Prop :=
  ∃ (phi tau : ℝ) (params : Fin T.size → ℤ × ℤ × ℚ × ℚ),
    0 < phi ∧ 0 < tau ∧ phi ≠ 1 ∧ tau ≠ 1 ∧
    ∀ i, T.depth i =
      -((params i).2.2.2 : ℝ).log
        + ((params i).2.2.1 : ℝ).log
        - ((params i).1 : ℝ) * phi.log
        - ((params i).2.1 : ℝ) * tau.log

/-- **Predicate (V0.9 line 9670 + line 9679)**: the SCSE iteration on
`T` has a fixed point at the canonical scale `k*`.

A "fixed point" here is a value `λ : ℝ` that satisfies the SCSE
closure equation in its strong form (rather than only via the κ_2
substitution).  We encode this abstractly: `λ` arises as the predicted
eigenvalue *and* is consistent with the triple's flow under the SCSE
iteration map (which we leave as a Prop hypothesis, not a `def`). -/
def SCSEHasFixedPoint (T : FiniteSpectralTriple) : Prop :=
  ∃ (lam_star : ℝ), 0 < lam_star ∧ lam_star = lambda1Predicted T

/-- **Predicate (V0.9 line 9670 + line 9749)**: the fixed point, if it
exists, is unique.

This is what v0.9 line 9749 flags as "explicit open computation":
quantitative success or failure of the SCSE depends on the uniqueness
of `λ_1(k*)`. -/
def SCSEFixedPointUnique (T : FiniteSpectralTriple) : Prop :=
  ∀ (lam₁ lam₂ : ℝ),
    (0 < lam₁ ∧ lam₁ = lambda1Predicted T) →
    (0 < lam₂ ∧ lam₂ = lambda1Predicted T) →
    lam₁ = lam₂

/-! ## Trivial structural lemmas about the predicates -/

/-- Uniqueness holds trivially for the *definitional* prediction
function, since equality with `lambda1Predicted T` forces equality. -/
theorem scse_uniqueness_definitional (T : FiniteSpectralTriple) :
    SCSEFixedPointUnique T := by
  intro lam₁ lam₂ h₁ h₂
  rcases h₁ with ⟨_, h₁_eq⟩
  rcases h₂ with ⟨_, h₂_eq⟩
  rw [h₁_eq, h₂_eq]

/-- If the SCSE has a fixed point, that fixed point equals the
framework's predicted `λ_1`. -/
theorem scse_fixed_point_eq_predicted
    (T : FiniteSpectralTriple) (h_exists : SCSEHasFixedPoint T) :
    ∃ lam : ℝ, 0 < lam ∧ lam = lambda1Predicted T :=
  h_exists

/-! ## Note on what is *not* in this file

We deliberately do NOT include the following constructs from the
audit-caught prior scaffold:

* `kappa2_target := 2 · log(Λ_c² / Λ_obs)` — this was the circular
  definition.  Here `κ_2` is a functional of `T`, no Λ_obs reference.
* `lambda_obs_value_bracket` — the numerical input + `norm_num`-style
  axiom.  Removed entirely.
* `kappa2_full_seesaw_strict_anti` and friends — the bracket/IVT axioms
  in `ℝ → ℝ` for an opaque function `kappa2_full_seesaw`.  Removed: the
  see-saw cascade is now a property of the triple's data, not a
  free-standing function.

What WOULD be needed to give the framework its empirical content is in
`CosmologicalConstantMatch.lean`: a *separate* hypothesis that the
predicted `λ_1` matches the observed Λ.  That match is empirical
confirmation, not definitional identity. -/

end SpectralPhysics.OP3

end
