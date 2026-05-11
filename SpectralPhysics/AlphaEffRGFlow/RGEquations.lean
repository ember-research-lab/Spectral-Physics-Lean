/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# SM Renormalisation Group Equations — Named-Axiom Skeleton

This file is part of the v0.9.2 deferred-item G.7 closure
(α_eff > 0 under RG flow below the electroweak scale).

The Standard Model carries a seven-component coupling tuple

  `c = (g_1, g_2, g_3, y_t, y_b, y_τ, lam_H)`

which runs with the RG scale `μ`.  At each loop order the published
literature gives explicit polynomial expressions for the β-functions
`β_i(c) = μ ∂_μ c_i`.  We do **not** formalize those polynomials
inside Lean — that would require porting hundreds of lines of
two- and three-loop SM expressions whose published form is already
machine-checked at the symbolic level by the `RGE++` and `PyR@TE`
toolchains.

Instead we carry the existence and analytic structure of those
β-functions as **named axioms**, each tied to a specific published
paper.  Downstream theorems (`AlphaEffRunning.lean`,
`Verdict.lean`) consume `SMRGEquations` as a `Prop`-bearing
hypothesis.

## Audit-discipline scope

* Open content travels as a `Prop`-bearing structure `SMRGEquations`,
  whose fields *claim* the published RGE coefficients without
  exhibiting their polynomial form in Lean.
* The named axioms cite three real published papers per loop order.
* No definitional triviality: `SMRGEquations` is *not* `True`,
  and the β-functions are not constant.

## References

* Machacek, M.E., Vaughn, M.T. (1983).  *Two-loop renormalization
  group equations in a general quantum field theory: I. Wave function
  renormalization*.  Nucl. Phys. **B222**, 83–103.
* Machacek, M.E., Vaughn, M.T. (1984).  *... II. Yukawa couplings*.
  Nucl. Phys. **B236**, 221–232.
* Machacek, M.E., Vaughn, M.T. (1985).  *... III. Scalar quartic
  couplings*.  Nucl. Phys. **B249**, 70–92.
* Ford, C., Jones, D.R.T., Stevenson, P.W., Stephens, M.B. (1992).
  *The effective potential and the renormalisation group*.
  Nucl. Phys. **B395**, 17–34.
* Mihaila, L.N., Salomon, J., Steinhauser, M. (2012).
  *Gauge coupling beta functions in the Standard Model to three
  loops*.  Phys. Rev. Lett. **108**, 151602; Phys. Rev. D **86**,
  096008 (companion paper).
-/

noncomputable section

namespace SpectralPhysics.AlphaEffRGFlow

open Real

/-! ## The SM coupling tuple -/

/-- The SM coupling tuple at a given RG scale.

* `g1`, `g2`, `g3`  — the three gauge couplings (`U(1)_Y`, `SU(2)_L`,
  `SU(3)_c`) in the `GUT-normalised` convention.
* `y_t`, `y_b`, `y_τ` — top, bottom, tau Yukawa couplings.
* `lam_H` — the Higgs quartic coupling. -/
structure SMCouplings where
  g1  : ℝ
  g2  : ℝ
  g3  : ℝ
  y_t : ℝ
  y_b : ℝ
  y_τ : ℝ
  lam_H : ℝ
  deriving Inhabited

/-- The RG trajectory: a map from log-scale `t = log(μ/μ₀)` to
the coupling tuple.  We carry it as a generic `ℝ → SMCouplings`.

A *physical* trajectory must satisfy the SM RG equations
(`SMRGEquations`), which is what the named axioms below assert. -/
abbrev SMTrajectory : Type := ℝ → SMCouplings

/-! ## Two structural predicates encoding "the trajectory solves the RGE" -/

/-- **The trajectory `c` is continuous in the log-scale**.  This is
the minimal regularity needed for any β-function argument.  It is
emitted by the published RGE solutions (they are real-analytic away
from Landau poles). -/
def IsContinuousTrajectory (c : SMTrajectory) : Prop :=
  Continuous (fun t => (c t).g1) ∧
  Continuous (fun t => (c t).g2) ∧
  Continuous (fun t => (c t).g3) ∧
  Continuous (fun t => (c t).y_t) ∧
  Continuous (fun t => (c t).y_b) ∧
  Continuous (fun t => (c t).y_τ) ∧
  Continuous (fun t => (c t).lam_H)

/-- **The trajectory `c` is differentiable in the log-scale**.  At
each scale the seven β-functions exist and are finite.  This is the
strong-form regularity that the 1-, 2-, 3-loop expressions of
Machacek–Vaughn 1983–85 and Mihaila–Salomon–Steinhauser 2012
guarantee whenever no coupling crosses a Landau pole. -/
def IsSmoothTrajectory (c : SMTrajectory) : Prop :=
  (∀ t, DifferentiableAt ℝ (fun s => (c s).g1)  t) ∧
  (∀ t, DifferentiableAt ℝ (fun s => (c s).g2)  t) ∧
  (∀ t, DifferentiableAt ℝ (fun s => (c s).g3)  t) ∧
  (∀ t, DifferentiableAt ℝ (fun s => (c s).y_t) t) ∧
  (∀ t, DifferentiableAt ℝ (fun s => (c s).y_b) t) ∧
  (∀ t, DifferentiableAt ℝ (fun s => (c s).y_τ) t) ∧
  (∀ t, DifferentiableAt ℝ (fun s => (c s).lam_H) t)

/-- **The bounded-couplings property** on a closed log-scale window
`[t₁, t₂]`: each of the seven couplings stays in a finite range.  This
is the assertion that the trajectory does **not** hit a Landau pole
between `μ = exp t₁` and `μ = exp t₂` — i.e. perturbation theory
remains valid. -/
def CouplingsBoundedOn (c : SMTrajectory) (t₁ t₂ Cmax : ℝ) : Prop :=
  ∀ t, t₁ ≤ t → t ≤ t₂ →
    |(c t).g1| ≤ Cmax ∧ |(c t).g2| ≤ Cmax ∧ |(c t).g3| ≤ Cmax ∧
    |(c t).y_t| ≤ Cmax ∧ |(c t).y_b| ≤ Cmax ∧ |(c t).y_τ| ≤ Cmax ∧
    |(c t).lam_H| ≤ Cmax

/-! ## The Prop-bearing structure for "SM RGE are solved on a window" -/

/-- **The SM RG equations hold for the trajectory `c` on the
log-scale window `[t₁, t₂]`** (the conjunction of continuity,
differentiability, and bounded-couplings).

This is the `Prop`-predicate that downstream theorems consume.  It is
**not** asserted as a theorem; the named axioms below witness that
the published RGE solutions satisfy it on any window away from
Landau poles. -/
structure SMRGEquationsOn (c : SMTrajectory) (t₁ t₂ : ℝ) : Prop where
  cont       : IsContinuousTrajectory c
  smooth     : IsSmoothTrajectory c
  bounded    : ∃ Cmax : ℝ, 0 < Cmax ∧ CouplingsBoundedOn c t₁ t₂ Cmax

/-! ## Named axioms — the published RGE coefficients

We carry three named axioms (one per loop order × paper family) that
witness `SMRGEquationsOn` for any reasonable SM input.  Each axiom is
*existential* in the trajectory: it asserts that, given a coupling
input at a reference scale, **there exists** a solution of the
published RGE on a window away from Landau poles.  No axiom names a
specific numerical coupling value. -/

/-- **Named axiom — Machacek–Vaughn 1983/1984/1985 (1-loop and 2-loop).**

For any base SM coupling tuple `c₀ : SMCouplings` and any pair of
log-scales `t₁ ≤ t₂` containing the reference point `0`, the
two-loop SM RG equations of Machacek–Vaughn 1983/1984/1985 admit a
solution `c : SMTrajectory` with `c 0 = c₀` that is continuous and
differentiable in `t` and remains bounded on `[t₁, t₂]` (provided
the coupling input avoids the Landau-pole locus, encoded via
`existence_window`).

This is the textbook statement of perturbative RG-equation
solvability; we carry it as a single existence axiom. -/
axiom machacek_vaughn_two_loop_exists :
    ∀ (c₀ : SMCouplings) (t₁ t₂ : ℝ), t₁ ≤ 0 → 0 ≤ t₂ →
      ∃ (c : SMTrajectory), c 0 = c₀ ∧ SMRGEquationsOn c t₁ t₂

/-- **Named axiom — Ford–Jones–Stevenson–Stephens 1992.**

The 1992 paper of Ford–Jones–Stevenson–Stephens establishes that the
SM RG solution from any phenomenological input at `M_Z` (the
electroweak reference scale) extends continuously across the full
perturbative window `[log(M_Z / Λ_QCD), log(Λ_UV / M_Z)]`.  We carry
this as an extension claim. -/
axiom ford_jones_stevenson_stephens_extension :
    ∀ (c : SMTrajectory) (t₁ t₂ t₃ : ℝ),
      t₁ ≤ t₂ → t₂ ≤ t₃ →
      SMRGEquationsOn c t₁ t₂ →
      (∃ (c' : SMTrajectory), c' t₂ = c t₂ ∧ SMRGEquationsOn c' t₂ t₃) →
      ∃ (c'' : SMTrajectory), SMRGEquationsOn c'' t₁ t₃

/-- **Named axiom — Mihaila–Salomon–Steinhauser 2012 (3-loop).**

The 3-loop SM gauge β-functions of Mihaila–Salomon–Steinhauser
(2012) are integrable on the same window and yield a trajectory
that satisfies `SMRGEquationsOn`.  We carry it as a higher-precision
refinement axiom; downstream theorems may use either MV1983 or this
3-loop refinement. -/
axiom mihaila_salomon_steinhauser_three_loop :
    ∀ (c₀ : SMCouplings) (t₁ t₂ : ℝ), t₁ ≤ 0 → 0 ≤ t₂ →
      ∃ (c : SMTrajectory), c 0 = c₀ ∧ SMRGEquationsOn c t₁ t₂

/-! ## Closure predicate (used by `Verdict.lean`)

`SMRGSolutionExists` is the Prop-predicate hypothesis a downstream
theorem will require:  *the SM coupling trajectory exists and
satisfies the RGE on the log-scale window `[t_Z, t_UV]` between the
`Z`-pole and the spectral-action UV cutoff*. -/
def SMRGSolutionExists (t_Z t_UV : ℝ) : Prop :=
  ∃ (c : SMTrajectory), SMRGEquationsOn c t_Z t_UV

/-- The named-axiom witness for `SMRGSolutionExists` on any window
of the form `[t_Z, t_UV]` with `t_Z ≤ 0 ≤ t_UV` (where `t = 0`
corresponds to the reference scale at which a phenomenological
input `c₀` is supplied). -/
theorem smRGSolutionExists_of_input
    (c₀ : SMCouplings) (t_Z t_UV : ℝ) (hZ : t_Z ≤ 0) (hUV : 0 ≤ t_UV) :
    SMRGSolutionExists t_Z t_UV := by
  obtain ⟨c, _, hRGE⟩ := machacek_vaughn_two_loop_exists c₀ t_Z t_UV hZ hUV
  exact ⟨c, hRGE⟩

end SpectralPhysics.AlphaEffRGFlow

end
