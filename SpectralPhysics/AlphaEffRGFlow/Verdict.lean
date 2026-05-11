/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.AlphaEffRGFlow.AlphaEffRunning
import SpectralPhysics.AlphaEffRGFlow.SignFlipRiskAnalysis

/-!
# v0.9.2 G.7 verdict — α_eff > 0 under RG flow below EW

This file assembles the verdict for v0.9.2 deferred item G.7
(α_eff > 0 below the electroweak scale).

## Verdict: CONDITIONAL — three-hypothesis closure under named axioms

The headline statement `alpha_eff_verdict_v092_G7` is a conditional
theorem of the form

  `(h_RGE : H_RGE)  (h_decoupling : H_Decoupling)
   (h_transport : ∀ c …)`
      ⇒  `∃ c, ∀ t ∈ [t_Z, t_UV], αEffAt c t > 0`.

The three hypotheses correspond directly to the three audit-discipline
buckets:

1. **`h_RGE`** — the SM RG equations admit a solution on the
   log-scale window (named axioms: Machacek–Vaughn 1983/84/85,
   Ford–Jones–Stevenson–Stephens 1992, Mihaila–Salomon–Steinhauser
   2012).
2. **`h_decoupling`** — heavy SM particles decouple at the four
   thresholds `m_t, m_H, m_b, m_τ` (named axiom: Manohar–Wise 2000).
3. **`h_transport`** — the regulator coefficient `α_eff` is
   continuous, boundary-matches at the cutoff, and is **strictly
   positive on the window**.  This is the open content; closure
   requires either a Python/mpmath sidecar (Route 1) or a
   β-function inequality (Route 2), neither of which is provided
   by this branch.

## Honest disclaimer

This Lean closure **does not** close the framework's empirical
question.  It only formalises the route:  *given* the three
hypotheses, positivity on the window is a Lean-checkable theorem.

The substantive empirical step — actually proving
`AlphaEffTransport c t_Z t_UV` for the framework's preferred
trajectory — is **deferred to a sidecar**.  See `STATUS.md` for the
recommended sidecar location:
`yukawa/pre_geometric/alpha_eff_RG_below_EW/`.

## Named axioms used (4 total)

| Axiom (file)                                      | Citation                       |
| ------------------------------------------------- | ------------------------------ |
| `machacek_vaughn_two_loop_exists` (`RGEquations`) | Machacek–Vaughn 1983/84/85     |
| `ford_jones_stevenson_stephens_extension` (`RGE`) | Ford–Jones–Stevenson–Stephens 92 |
| `mihaila_salomon_steinhauser_three_loop` (`RGE`)  | Mihaila–Salomon–Steinhauser 2012 |
| `manohar_wise_decoupling` (`DecouplingThreshold`) | Manohar–Wise 2000              |

## Comparison to the audit-discipline reference branches

| Aspect                | Reference (`KSRCompactness`) | This module                              |
| --------------------- | ---------------------------- | ---------------------------------------- |
| Verdict               | CONDITIONAL                  | CONDITIONAL                              |
| Number of named axioms | 1                            | 4                                        |
| Closure form          | 1 predicate → 1 named axiom  | 3 predicates → 4 named axioms            |
| Sidecar required      | No                           | **Yes** (Python/mpmath, see STATUS.md)   |
-/

noncomputable section

namespace SpectralPhysics.AlphaEffRGFlow

open Real

/-! ## Headline verdict (type-checked) -/

/-- **THE α_eff > 0 BELOW EW VERDICT (CONDITIONAL, honest).**

For every log-scale window `[t_Z, t_UV]` with `t_Z ≤ t_UV`, given:

* **H1 (RGE)**: the SM RG equations admit a solution `c` on the
  window (Machacek–Vaughn 1983/84/85, Ford–Jones–Stevenson–Stephens
  1992, Mihaila–Salomon–Steinhauser 2012);
* **H2 (Decoupling)**: that solution satisfies the matching
  conditions at the SM-below-EW thresholds (Manohar–Wise 2000);
* **H3 (Transport)**: the regulator coefficient `α_eff` is
  continuous, boundary-matches at the cutoff, and is strictly
  positive on the window.

The conclusion is:  **there exists a trajectory `c` such that
`αEffAt c t > 0` for every `t ∈ [t_Z, t_UV]`**.

This is the *predicate-hypothesis* form of v0.9 line 16805's
expectation.  Closure of the framework's empirical question requires
discharging H3 quantitatively — a sidecar task. -/
theorem alpha_eff_verdict_v092_G7
    (t_Z t_UV : ℝ) (hwin : t_Z ≤ t_UV)
    (h_RGE        : H_RGE t_Z t_UV)
    (h_decoupling : H_Decoupling t_Z t_UV)
    (h_transport  : ∀ (c : SMTrajectory),
        SMRGEquationsOn c t_Z t_UV →
        DecouplingAtThresholds c →
        AlphaEffTransport c t_Z t_UV) :
    ∃ (c : SMTrajectory), ∀ t, t_Z ≤ t → t ≤ t_UV → 0 < αEffAt c t :=
  alpha_eff_remains_positive_below_EW t_Z t_UV hwin h_RGE h_decoupling
    h_transport

/-! ## Cutoff-positivity entry point

The third hypothesis `h_transport` packages cutoff-positivity through
its `boundary` and `signStable` fields evaluated at `t_UV`.  The
following lemma exposes that entry point cleanly:  *given* the
transport hypothesis, the cutoff value `alphaEffAtCutoff` is
positive (consistent with v0.9 `SeeleyDeWitt/STATUS.md`). -/
theorem cutoff_positivity_from_verdict
    (c : SMTrajectory) (t_Z t_UV : ℝ) (hwin : t_Z ≤ t_UV)
    (hT : AlphaEffTransport c t_Z t_UV) :
    0 < alphaEffAtCutoff := by
  have h1 := hT.boundary
  have h2 := hT.signStable t_UV hwin (le_refl t_UV)
  rw [h1] at h2
  exact h2

/-! ## Existence-form, parameterised by a phenomenological input -/

/-- **Trajectory-existence form** (the form a sidecar would consume).

Given:
* an input coupling tuple `c₀ : SMCouplings` at the reference scale
  `t = 0` (typically PDG 2024 values at `M_Z`);
* a log-scale window `[t_Z, t_UV]` containing 0 and the four
  SM-below-EW thresholds;
* the transport hypothesis;

there exists a trajectory `c` solving the SM RGE, satisfying the
decoupling matching, and yielding `α_eff > 0` on the window.

This is the form the sidecar Python script verifies numerically. -/
theorem alpha_eff_verdict_existence_form
    (c₀ : SMCouplings) (t_Z t_UV : ℝ)
    (hZ : t_Z ≤ 0) (hUV : 0 ≤ t_UV) (_hwin : t_Z ≤ t_UV)
    (hbot : t_Z ≤ Real.log (m_tau / M_Z))
    (htop : Real.log (m_top / M_Z) ≤ t_UV)
    (h_transport : ∀ (c : SMTrajectory),
        SMRGEquationsOn c t_Z t_UV →
        DecouplingAtThresholds c →
        AlphaEffTransport c t_Z t_UV) :
    ∃ (c : SMTrajectory), ∀ t, t_Z ≤ t → t ≤ t_UV → 0 < αEffAt c t := by
  -- Step 1: existence of a trajectory solving the SM RGE
  --         (named axiom: `machacek_vaughn_two_loop_exists`).
  obtain ⟨c, _hc0, hRGE⟩ :=
    machacek_vaughn_two_loop_exists c₀ t_Z t_UV hZ hUV
  -- Step 2: decoupling at the thresholds for that trajectory
  --         (named axiom: `manohar_wise_decoupling`).
  have hDec : DecouplingAtThresholds c :=
    decouplingAtThresholds_of_window c t_Z t_UV hRGE hbot htop
  -- Step 3: the transport hypothesis discharges sign-stability.
  refine ⟨c, ?_⟩
  intro t ht1 ht2
  exact (h_transport c hRGE hDec).signStable t ht1 ht2

/-! ## Sidecar pointer

The empirical-quantitative closure lives outside Lean.  The
recommended location for the Python/mpmath RG-running sidecar
(documented in `STATUS.md`) is

  `yukawa/pre_geometric/alpha_eff_RG_below_EW/`

We do not create that directory in this branch. -/

/-- **Trivial pointer theorem** — records (as a `True` statement) the
sidecar location for downstream documentation tooling. -/
theorem sidecar_pointer : True := trivial

end SpectralPhysics.AlphaEffRGFlow

end
