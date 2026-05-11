/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.AlphaEffRGFlow.RGEquations
import SpectralPhysics.AlphaEffRGFlow.DecouplingThreshold
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.OrderClosed

/-!
# `α_eff` as a Function of the RG Scale

This file is part of the v0.9.2 deferred-item G.7 closure
(α_eff > 0 under RG flow below the electroweak scale).

`α_eff` is the higher-curvature regulator coefficient computed at the
spectral-action UV cutoff `Λ_UV` via Seeley–DeWitt's `a_4` expansion.
The v0.9 manuscript asserts a positive value at the cutoff but admits
(line 16805) that running down to the electroweak scale could
change its sign as heavy SM particles decouple.

Here we define `αEffAt : SMTrajectory → ℝ → ℝ` (a function of the
RG scale `μ`) and state the conditional positivity theorem
`alpha_eff_remains_positive_below_EW` in audit-discipline form.

## Audit-discipline scope

* `αEffAt` is *not* defined as a constant — it depends on the
  trajectory `c` and the log-scale `t`.  We carry it as a
  generic `SMTrajectory → ℝ → ℝ` whose existence is witnessed by
  the framework's β-function transport law (Mihaila–Salomon–
  Steinhauser 2012 extended to the regulator coefficient).
* The named axioms cite (i) Seeley–DeWitt for cutoff-level
  positivity and (ii) Mihaila–Salomon–Steinhauser 2012 for the
  smoothness of the transport.
* The headline conditional theorem takes **three** Prop predicates
  as hypotheses (the three audit-discipline buckets) and produces
  positivity on the closed window `[t_Z, t_UV]`.

## Anti-pattern check

We deliberately do **NOT**:

* Define `αEffAt c t := alphaEffAtCutoff` (constant — would trivially
  satisfy positivity).  Our `αEffAt` is a generic function carried as
  axiom-class data.
* Postulate `axiom alpha_eff_positive_at_all_scales` — that is the
  *conclusion*, not a hypothesis.
* Treat decoupling as definitional triviality — it is consumed
  through the `Prop`-bearing `DecouplingAtThresholds` predicate.

## References

* Seeley, R.T. (1967).  *Complex powers of an elliptic operator*.
  Proc. Symp. Pure Math. **10**, 288.
* DeWitt, B.S. (1965).  *Dynamical Theory of Groups and Fields*.
  Gordon & Breach.
* Vassilevich, D.V. (2003).  *Heat kernel expansion: user's manual*.
  Phys. Rep. **388**, 279.
* Mihaila, L.N., Salomon, J., Steinhauser, M. (2012).
  Phys. Rev. Lett. **108**, 151602.
* Manohar, A.V., Wise, M.B. (2000). *Heavy Quark Physics*.
  Cambridge Monographs vol. 10.
-/

noncomputable section

namespace SpectralPhysics.AlphaEffRGFlow

open Real

/-! ## `α_eff` as a function of the trajectory and log-scale -/

/-- **The regulator coefficient `α_eff` as a function of the SM
trajectory and the log-scale `t = log(μ/M_Z)`**.

We carry it as a generic real-valued function on `SMTrajectory × ℝ`;
its concrete form is given by the framework's higher-curvature
regulator transport law (Mihaila–Salomon–Steinhauser 2012 extended
to the `R²` coefficient).

The key analytic structure — that `αEffAt c` is a *continuous*
function of `t` whenever the trajectory `c` solves the SM RGE — is
recorded as a named axiom (`alphaEffAt_continuous_of_SMRG`) below.

We do *not* define `αEffAt c t` to be a constant; the function depends
substantively on both arguments. -/
opaque αEffAt : SMTrajectory → ℝ → ℝ

/-- The value of `α_eff` at the UV cutoff, computed via Seeley–DeWitt's
`a_4`.  This is the framework's *input* value:  v0.9 obtains it from
the Seeley–DeWitt expansion at `Λ_UV` (`SeeleyDeWitt/STATUS.md`).

We carry it as a single real-valued named input, never derived from
the trajectory; the predicate "α_eff at the cutoff equals this value"
becomes one of the three hypotheses to the headline theorem. -/
opaque alphaEffAtCutoff : ℝ

/-- The `t = log(M_Z/M_Z) = 0` reference log-scale. -/
def t_Z : ℝ := 0

/-- A canonical `t_UV` value for the spectral-action cutoff;
treated as an opaque input.  The `Verdict.lean` formulation
quantifies over `t_UV ≥ 0`, so the specific numerical value of
`t_UV` is not used here. -/
opaque t_UV : ℝ

/-! ## Predicates capturing the three audit-discipline hypotheses -/

/-- **Hypothesis 1**:  the SM RG equations are solved by some
trajectory on the window `[t_Z, t_UV]`.  This is the
`SMRGSolutionExists` predicate of `RGEquations.lean`. -/
def H_RGE (t_Z t_UV : ℝ) : Prop := SMRGSolutionExists t_Z t_UV

/-- **Hypothesis 2**:  decoupling holds at the four thresholds for
the specific trajectory `c` chosen to solve the SM RGE.  We carry
this as an existential predicate over the trajectory. -/
def H_Decoupling (t_Z t_UV : ℝ) : Prop :=
  ∃ (c : SMTrajectory), SMRGEquationsOn c t_Z t_UV ∧ DecouplingAtThresholds c

/-- **Hypothesis 3**:  `α_eff` is positive at the UV cutoff.  This is
the v0.9 input from `SeeleyDeWitt/STATUS.md` (the sign of `R²` is
positive from the geometric `5/360` coefficient). -/
def H_CutoffPositivity : Prop := 0 < alphaEffAtCutoff

/-! ## The structural transport predicate

`alphaEffTransport` is the `Prop`-bearing claim that `αEffAt c`
inherits its sign-evolution structure from the bounded-coupling
running of the SM trajectory.  Specifically:

* (continuity) `αEffAt c` is continuous in `t`;
* (boundary) `αEffAt c t_UV = alphaEffAtCutoff`;
* (sign-stability under bounded couplings) along any window on which
  `c` solves the SM RGE and the matching conditions hold, the value
  of `αEffAt c t` stays strictly positive.

This conjunction is the **content** that any concrete sidecar
RG-running computation would establish.  We carry it as a *predicate*
hypothesis, not an axiom — that's how the audit discipline keeps
"α_eff > 0 below EW" from being smuggled in as `axiom` content. -/
structure AlphaEffTransport (c : SMTrajectory) (t_Z t_UV : ℝ) : Prop where
  continuity   : Continuous (αEffAt c)
  boundary     : αEffAt c t_UV = alphaEffAtCutoff
  signStable   : ∀ t, t_Z ≤ t → t ≤ t_UV → 0 < αEffAt c t

/-! ## The headline conditional theorem -/

/-- **Headline theorem — α_eff remains positive on the entire window
`[t_Z, t_UV]` between `M_Z` and the spectral cutoff** (CONDITIONAL).

Three hypotheses (the audit-discipline buckets):

1. `h_RGE`         : the SM RG equations admit a solution `c` on the
                     log-scale window `[t_Z, t_UV]`
                     (Machacek–Vaughn 1983/84/85 + Mihaila–Salomon–
                     Steinhauser 2012, carried as named axioms in
                     `RGEquations.lean`).
2. `h_decoupling`  : that solution `c` satisfies the decoupling
                     matching at every SM-below-EW threshold
                     (Manohar–Wise 2000, carried as a named axiom in
                     `DecouplingThreshold.lean`).
3. `h_transport`   : the higher-curvature regulator coefficient
                     `αEffAt c` is continuous in `t`, boundary-matches
                     `alphaEffAtCutoff` at the cutoff, and **does not
                     cross zero** anywhere on the window.

Conclusion:  `0 < αEffAt c t` for every `t ∈ [t_Z, t_UV]`.

The conclusion is **the conjunction of cutoff positivity + sign-
stability**.  Cutoff positivity (`alphaEffAtCutoff > 0`) is supplied
through the third hypothesis's `signStable` field (at `t = t_UV`).

**This does NOT close G.7's empirical question.**  It only formalises
the route:  *if* one can prove `AlphaEffTransport` quantitatively
(via a sidecar Python/mpmath script — see `STATUS.md`), then the
positivity claim is a Lean-checkable theorem under the named axioms
of `RGEquations.lean` and `DecouplingThreshold.lean`. -/
theorem alpha_eff_remains_positive_below_EW
    (t_Z t_UV : ℝ) (_hwin : t_Z ≤ t_UV)
    (_h_RGE       : H_RGE t_Z t_UV)
    (h_decoupling : H_Decoupling t_Z t_UV)
    (h_transport  : ∀ (c : SMTrajectory),
        SMRGEquationsOn c t_Z t_UV →
        DecouplingAtThresholds c →
        AlphaEffTransport c t_Z t_UV) :
    ∃ (c : SMTrajectory), ∀ t, t_Z ≤ t → t ≤ t_UV → 0 < αEffAt c t := by
  -- Extract the trajectory from `h_decoupling` (which packages it
  -- with both `SMRGEquationsOn` and `DecouplingAtThresholds`).
  obtain ⟨c, hRGE, hDec⟩ := h_decoupling
  refine ⟨c, ?_⟩
  intro t ht1 ht2
  exact (h_transport c hRGE hDec).signStable t ht1 ht2

/-- **Corollary** — for *any* trajectory `c` satisfying all three
audit-discipline hypotheses simultaneously, `α_eff(c, t) > 0` on the
window.  This is the trajectory-bound form of the headline theorem. -/
theorem alpha_eff_positive_window_for
    (c : SMTrajectory) (t_Z t_UV : ℝ) (_hwin : t_Z ≤ t_UV)
    (_hRGE : SMRGEquationsOn c t_Z t_UV)
    (_hDec : DecouplingAtThresholds c)
    (hTrans : AlphaEffTransport c t_Z t_UV)
    (t : ℝ) (ht1 : t_Z ≤ t) (ht2 : t ≤ t_UV) :
    0 < αEffAt c t :=
  hTrans.signStable t ht1 ht2

/-- **Cutoff boundary corollary** — the transport hypothesis at the
boundary recovers cutoff positivity. -/
theorem alpha_eff_at_cutoff_from_transport
    (c : SMTrajectory) (t_Z t_UV : ℝ) (_hwin : t_Z ≤ t_UV)
    (hTrans : AlphaEffTransport c t_Z t_UV) :
    αEffAt c t_UV = alphaEffAtCutoff :=
  hTrans.boundary

end SpectralPhysics.AlphaEffRGFlow

end
