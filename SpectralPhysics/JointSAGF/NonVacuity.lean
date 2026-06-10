/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom, Claude (Anthropic)
-/
import SpectralPhysics.JointSAGF.Barrier
import SpectralPhysics.JointSAGF.Basin
import SpectralPhysics.JointSAGF.TraceConstraint

/-!
# JointSAGF non-vacuity witnesses (adversarial audit)

Per the Alignment Gap Register discipline, every theorem whose hypotheses are
structural (type classes + functional hypotheses) must be shown *satisfiable*
on concrete data — otherwise a CLOSED verdict can hide a vacuously-true
statement. This file instantiates the JointSAGF chain on explicit witnesses:

* `sq_coercive` / `headline_nonvacuous` : the J6 headline
  `sagf_stationary_exists` fires on `E = ℝ`, `Sbase = 0`, `Str = x²`,
  `g = 2x` — and the stationary point it asserts is witnessed by `kstar = 0`.
* `coercivity_is_load_bearing` : dropping the coercivity hypothesis breaks
  the conclusion (`Str = id`, gradient constantly `1`, no stationary point) —
  the trace-coercivity hypothesis is doing real work, not decoration.
* `sagf_monotone_nonvacuous` : J1 fires on a NON-constant flow — the basin
  trajectory `x₀·exp(-2t)` of `S(x) = x²` (reusing `basin_relaxation`).
* `joint_kernel_monotone_nonvacuous` : the joint kernel space
  `JointKernelSpace 1 1 1` carries the required instances and J1
  instantiates on it.
* `barrier_nonvacuous` : J2 fires on a concrete 1-mode spectrum with the
  heat-kernel cutoff.

All witnesses are theorems in the root build; if a statement upstream drifts
into vacuity, this file breaks.
-/

noncomputable section

open Filter

namespace SpectralPhysics.JointSAGF.NonVacuity

/-! ### J6 headline: `sagf_stationary_exists` is non-vacuous -/

/-- The model trace term `x ↦ x²` is coercive on `ℝ`: the J6 coercivity
hypothesis `Tendsto Str (cocompact E) atTop` is satisfiable. -/
theorem sq_coercive : Tendsto (fun x : ℝ => x ^ 2) (cocompact ℝ) atTop := by
  have h := (tendsto_pow_atTop (two_ne_zero)).comp
    (tendsto_norm_cocompact_atTop (E := ℝ))
  simpa [Function.comp_def, Real.norm_eq_abs, sq_abs] using h

/-- Gradient witness: `x ↦ 0 + x²` has gradient `2x` at every point. -/
theorem quad_hasGradient (x : ℝ) :
    HasGradientAt (fun y : ℝ => (fun _ : ℝ => (0 : ℝ)) y + y ^ 2) (2 * x) x := by
  have h : HasDerivAt (fun y : ℝ => 0 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add (0 : ℝ)
  exact h.hasGradientAt'

/-- **Headline witness.** `sagf_stationary_exists` fires on concrete data:
`E = ℝ`, `Sbase = 0` (bounded below by `0`), `Str = x²` (coercive),
gradient `g = 2x`. The hypothesis set of the J6 headline is satisfiable. -/
theorem headline_nonvacuous : ∃ kstar : ℝ, 2 * kstar = 0 :=
  sagf_stationary_exists (fun _ => 0) (fun x => x ^ 2) (fun x => 2 * x) 0
    (fun _ => le_refl 0) sq_coercive quad_hasGradient

/-- The stationary point the headline asserts is explicitly `kstar = 0`. -/
example : 2 * (0 : ℝ) = 0 := by norm_num

/-- **Adversarial check: coercivity is load-bearing.** Replace the coercive
trace `x²` by the non-coercive `Str = id` (everything else as in the
headline: base bounded below, gradient exists everywhere — here constantly
`1`) and the conclusion FAILS: there is no stationary point. So the J6
headline is not provable from the remaining hypotheses; the trace-coercivity
hypothesis carries the existence content. -/
theorem coercivity_is_load_bearing :
    (∀ x : ℝ, HasGradientAt (fun y : ℝ => (fun _ : ℝ => (0 : ℝ)) y + y)
      ((fun _ : ℝ => (1 : ℝ)) x) x)
    ∧ ¬ ∃ kstar : ℝ, (fun _ : ℝ => (1 : ℝ)) kstar = 0 := by
  constructor
  · intro x
    have h : HasDerivAt (fun y : ℝ => 0 + y) (1 : ℝ) x := by
      simpa using (hasDerivAt_id x).const_add (0 : ℝ)
    exact h.hasGradientAt'
  · rintro ⟨k, hk⟩
    exact one_ne_zero hk

/-! ### J1: monotonicity is non-vacuous on a non-constant flow -/

/-- **J1 witness (non-constant).** The basin trajectory `x₀·exp(-2t)` is a
genuine gradient-flow trajectory for `S(x) = x²` (gradient `2x`), and
`sagf_monotone` fires on it: `t ↦ (x₀·exp(-2t))²` is antitone. Reuses
`basin_relaxation` (J5b) as the velocity check — the J1 and J5 layers
compose on the same witness. -/
theorem sagf_monotone_nonvacuous (x₀ : ℝ) :
    Antitone fun t => (x₀ * Real.exp (-2 * t)) ^ 2 :=
  sagf_monotone (fun x => x ^ 2)
    (fun t => x₀ * Real.exp (-2 * t))
    (fun t => 2 * (x₀ * Real.exp (-2 * t)))
    (fun t => by simpa using (hasDerivAt_pow 2 (x₀ * Real.exp (-2 * t))).hasGradientAt')
    (fun t => by simpa [neg_mul] using basin_relaxation 2 x₀ t)

/-- **J1 joint-space witness.** `JointKernelSpace 1 1 1` (3 edge
coordinates) carries the inner-product/complete instances the theorem
needs, and `joint_kernel_monotone` instantiates on it (constant flow at
the origin; hypothesis-satisfiability check for the instance chain). -/
theorem joint_kernel_monotone_nonvacuous :
    Antitone fun _ : ℝ => (fun _ : JointKernelSpace 1 1 1 => (0 : ℝ)) 0 :=
  joint_kernel_monotone 1 1 1 (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => hasGradientAt_const _ _)
    (fun t => by simpa using hasDerivAt_const t (0 : JointKernelSpace 1 1 1))

/-! ### J2: the barrier inequality is non-vacuous on a concrete spectrum -/

/-- **J2 witness.** One mode, heat-kernel cutoff, eigenvalue pushed from
`1` down to `0`: the spectral action strictly increases
(`exp(-1) < exp(0)`). Both J2 inequalities fire on concrete spectra. -/
theorem barrier_nonvacuous :
    ∑ k : Fin 1, Real.exp (-(fun _ : Fin 1 => (1 : ℝ)) k)
      < ∑ k : Fin 1, Real.exp (-(fun _ : Fin 1 => (0 : ℝ)) k) :=
  trace_f_strict_of_gap_collapse (fun x => Real.exp (-x)) exp_neg_antitone
    (fun _ => 1) (fun _ => 0) (fun _ => by norm_num) 0
    (by norm_num [Real.exp_lt_exp])

end SpectralPhysics.JointSAGF.NonVacuity
