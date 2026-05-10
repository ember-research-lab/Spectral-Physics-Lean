/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Cosmology.FriedmannEquation

/-!
# Perpetual Trace Activity (the user's reframe)

Under Route B's `c₁ = 1/2`, the SAGF trace-sector dispersion symbol
satisfies

  σ_tr(Λ; ξ)  >  0   for *all*  0 < ξ < Λ ,

i.e. the trace mode is anti-diffusive at *every* sub-Planckian
momentum.  In v0.9 this was framed as a "soft falsifier"
(recovering the Mottola–Polchinski conformal-mode problem rather
than Starobinsky inflation); the user has explicitly *reframed* this
as a *feature* — perpetual trace activity is the natural physical
content, not a bug.

This file type-checks the reframe by isolating, naming and proving
the three statements that operationalise it:

* `traceModePerpetuallyActive` — anti-diffusivity holds at every
  sub-Planckian ξ;
* `noStarobinskyBoundedRegime` — there is *no* sub-Planckian ξ at
  which σ_tr changes sign (i.e. the Starobinsky-bounded regime is
  *empty* below the spectral cutoff);
* `crossover_well_above_Planck` — the crossover is at least
  `100 · Λ²` away in momentum-squared, i.e. parametrically
  trans-Planckian.

Together these three theorems compose into the user's reframe
proposition: **the trace mode is a generic anti-diffusive mode of
SAGF across the full physical IR**.
-/

noncomputable section

namespace SpectralPhysics.Cosmology

/-! ## Statement 1: Trace mode is anti-diffusive at every sub-Planckian ξ -/

/-- **Perpetual trace activity.**  For every sub-Planckian momentum
`0 < ξ < Λ`, `σ_tr(Λ; ξ) > 0` — i.e. the trace mode is anti-diffusive
across the entire physical IR.  This is the *reframe*: the Route-B
verdict "ξ_cross trans-Planckian" interpreted as a feature, not a
bug. -/
theorem traceModePerpetuallyActive
    (Λ : ℝ) (hΛ : 0 < Λ) :
    ∀ ξ : ℝ, 0 < ξ → ξ < xiPlanck Λ → 0 < sigmaTr Λ ξ := by
  intro ξ hξ_pos hξ_sub
  exact sigmaTr_pos_subPlanckian Λ ξ hΛ hξ_pos hξ_sub

/-! ## Statement 2: No Starobinsky-bounded regime sub-Planckian -/

/-- **No sub-Planckian Starobinsky-bounded regime.**

There is no `ξ` with `0 < ξ < Λ` at which `σ_tr(Λ; ξ) ≤ 0`.  The
whole "Starobinsky bounded plateau" is *trans-Planckian*: it
exists only at ξ ≥ ξ_cross, which is far above the spectral cutoff. -/
theorem noStarobinskyBoundedRegime
    (Λ : ℝ) (hΛ : 0 < Λ) :
    ¬ ∃ ξ : ℝ, 0 < ξ ∧ ξ < xiPlanck Λ ∧ sigmaTr Λ ξ ≤ 0 := by
  rintro ⟨ξ, hξ_pos, hξ_sub, hξ_le⟩
  have h_pos : 0 < sigmaTr Λ ξ :=
    sigmaTr_pos_subPlanckian Λ ξ hΛ hξ_pos hξ_sub
  linarith

/-! ## Statement 3: Crossover is parametrically trans-Planckian -/

/-- **Crossover well above Planck.**  Concrete trans-Planckian gap. -/
theorem crossover_well_above_Planck
    (Λ : ℝ) (hΛ : 0 < Λ) :
    100 * Λ^2 < xiCrossSq Λ :=
  xiCrossSq_transPlanckian Λ hΛ

/-! ## Statement 4: Perpetually-active dispersion implies "tachyonic everywhere"

If we identify the (Wick-rotated) dispersion sign `σ_tr > 0` with
"tachyonic" (anti-diffusive in the gradient flow), then the
combination of `traceModePerpetuallyActive` and
`noStarobinskyBoundedRegime` says:  *every* sub-Planckian ξ is
tachyonic, with *no* sub-Planckian regulating regime.  This is the
"trace mode is a generic tachyonic mode of SAGF" picture from
`c1_and_5sector/verdict.md`. -/

/-- **Tachyonic-everywhere proposition.**

Define `tachyonicAt Λ ξ := 0 < sigmaTr Λ ξ` (anti-diffusive).  Then
for every sub-Planckian `ξ > 0`, `tachyonicAt Λ ξ` holds. -/
def tachyonicAt (Λ ξ : ℝ) : Prop := 0 < sigmaTr Λ ξ

theorem tachyonicAt_subPlanckian
    (Λ : ℝ) (hΛ : 0 < Λ) :
    ∀ ξ : ℝ, 0 < ξ → ξ < xiPlanck Λ → tachyonicAt Λ ξ := by
  intro ξ hξ_pos hξ_sub
  unfold tachyonicAt
  exact sigmaTr_pos_subPlanckian Λ ξ hΛ hξ_pos hξ_sub

/-! ## Composite reframe theorem

The full content of the user's reframe in one statement: across the
entire physical IR, the trace mode is anti-diffusive (perpetual
activity), *no* Starobinsky-bounded regime exists sub-Planckian,
and the regulating crossover is parametrically trans-Planckian. -/

/-- **The reframe theorem.**

For every spectral cutoff `Λ > 0`, three statements hold *together*:

1. perpetual trace activity:  `∀ 0 < ξ < Λ, σ_tr(Λ; ξ) > 0`;
2. no sub-Planckian regulating regime:  `¬ ∃ 0 < ξ < Λ, σ_tr ≤ 0`;
3. trans-Planckian crossover:  `100 · Λ² < ξ_cross²(Λ)`.

These together realise "perpetual trace activity" as a *feature*
of Route B's `c₁ = 1/2`. -/
theorem perpetual_trace_activity_reframe
    (Λ : ℝ) (hΛ : 0 < Λ) :
    (∀ ξ : ℝ, 0 < ξ → ξ < xiPlanck Λ → 0 < sigmaTr Λ ξ)
    ∧ (¬ ∃ ξ : ℝ, 0 < ξ ∧ ξ < xiPlanck Λ ∧ sigmaTr Λ ξ ≤ 0)
    ∧ (100 * Λ^2 < xiCrossSq Λ) :=
  ⟨traceModePerpetuallyActive Λ hΛ,
   noStarobinskyBoundedRegime Λ hΛ,
   crossover_well_above_Planck Λ hΛ⟩

/-! ## Connection to the Friedmann derivation

The Friedmann equation derivation (`friedmann_from_sigmaTr`) holds
*regardless* of whether the regime is Starobinsky-bounded or
perpetual-tachyonic: the conformal-frame transform is Whitt-1984
textbook material, and produces the Einstein-frame scalar action with
its scalaron potential.  What changes is the *interpretation* of the
result:

* If `ξ_cross` were sub-Planckian (v0.9's nominal "Starobinsky"
  branch, requiring `c₁ ∼ λ_σ ≪ 1`), then the inflationary plateau
  is a *physical* slow-roll branch.
* On Route B's `c₁ = 1/2`, the plateau is *trans-Planckian*; the
  inflationary phenomenology is then driven by the *nonlinear*
  dynamics of the perpetually-active trace mode (Remark 'basin' in
  v0.9).

The Lean derivation in `FriedmannEquation.lean` covers *both*
readings.  This file pins down the fact that on Route B we are in
the *perpetual-trace-activity* reading. -/

/-- **Combined reframe + Friedmann theorem.**

Given a positive cutoff `Λ` and a `ConformalFrameTransform Λ`
instance, both:

(i) the perpetual-trace-activity reframe holds;

(ii) the standard Friedmann evolution `Ḣ = −(κ²/2)(ρ+p)` follows
     for any Friedmann triple satisfying the first Friedmann + continuity
     equations on a non-vanishing-`H` regime. -/
theorem reframe_plus_friedmann
    (Λ : ℝ) (hΛ : 0 < Λ) [_inst : ConformalFrameTransform Λ] :
    -- the reframe
    ((∀ ξ : ℝ, 0 < ξ → ξ < xiPlanck Λ → 0 < sigmaTr Λ ξ)
     ∧ (¬ ∃ ξ : ℝ, 0 < ξ ∧ ξ < xiPlanck Λ ∧ sigmaTr Λ ξ ≤ 0)
     ∧ (100 * Λ^2 < xiCrossSq Λ))
    ∧
    -- the Friedmann evolution
    (∀ F : FriedmannTriple,
        FriedmannFirst F →
        FriedmannContinuity F →
        (∀ t, F.H t ≠ 0) →
        (∀ t, ∃ Hdot, HasDerivAt F.H Hdot t) →
        ∀ t, ∃ Hdot, HasDerivAt F.H Hdot t ∧
            Hdot = -(kappaSq / 2) * (F.ρ t + F.p t)) := by
  refine ⟨perpetual_trace_activity_reframe Λ hΛ, ?_⟩
  intro F hF hCont hH_ne hH_diff t
  exact friedmann_continuity_implies_Hdot F hF hCont hH_diff hH_ne t

end SpectralPhysics.Cosmology

end
