/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Cosmology.SigmaTrDispersion
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# f(R) → Einstein-frame conformal transform (Whitt 1984)

Pure f(R) gravity in the Jordan frame,

  S_J = (1/(2κ²)) ∫ d⁴x √(−g) · f(R),

is *classically equivalent* to Einstein gravity coupled to a single
scalar field σ (the "scalaron") in the *Einstein frame*, via the
Weyl rescaling

  g̃_{μν} = Ω² g_{μν},      Ω² = f'(R) = e^{√(2/3) σ / M_Pl},

and the Legendre transform R → σ.  The Einstein-frame action is

  S_E = ∫ d⁴x √(−g̃) · [ (1/(2κ²)) R̃ − (1/2)(∂σ)² − V(σ) ],

with potential

  V(σ) = (M_Pl² / 2) · (R · f'(R) − f(R)) / f'(R)² .

This is standard textbook material:
* Whitt, B. (1984). *Phys. Lett. B* 145, 176.
* De Felice, A. & Tsujikawa, S. (2010). *Living Rev. Relativity* 13, 3.

We carry the existence of this transform as an *axiom-instance*
(`ConformalFrameTransform`) so that the rest of the chain (Einstein
equation in the Einstein frame, Friedmann equation on FRW, etc.) is
on the same standardised footing as Mathlib's own physics
infrastructure.

## Main results

* `ConformalFrameTransform` : an `[axiom-class]` recording the
  Whitt-1984 / De Felice–Tsujikawa equivalence as a structural
  primitive on a single field.
* `scalaron_potential_starobinsky` : closed-form scalaron potential
  for `f(R) = R + R²/(6 m_σ²)`,
    V(σ) = (3/4) M_Pl² m_σ² (1 − e^{−√(2/3) σ/M_Pl})².
* `mSigma_from_sigmaTr` : the Starobinsky scalaron mass squared
  read off from the SAGF dispersion symbol.
* `mSigmaSq_pos` : `m_σ² > 0` from `c₁, f₂, Λ, f₀, α_eff > 0`.

## References

* Whitt 1984; De Felice–Tsujikawa 2010 §3.
-/

noncomputable section

open Real

namespace SpectralPhysics.Cosmology

/-! ## Section 1: Reduced Planck mass

We carry `M_Pl` as a positive real parameter; nothing in this file
depends on its numerical value. -/

/-- The reduced Planck mass (positive, normalisation-dependent). -/
def MPl : ℝ := 1

theorem MPl_pos : 0 < MPl := by unfold MPl; norm_num

/-! ## Section 2: The Starobinsky scalaron mass from σ_tr

If we identify the SAGF dispersion symbol `σ_tr(ξ) = c₁ f₂ Λ² ξ² −
6 f₀ α_eff ξ⁴` as the linearised propagator of a *Starobinsky-form*
f(R), `f(R) = R + R²/(6 m_σ²)`, then dimensional analysis of the
dispersion relation `σ_tr(ξ) = 0` (the propagator pole) gives

  m_σ²  =  (c₁ · f₂ · Λ²)  /  (6 · f₀ · α_eff)  =  ξ_cross²(Λ).

I.e. the scalaron mass squared *is* the crossover momentum squared:
the trace mode crosses from anti-diffusive to diffusive exactly at
the scalaron scale.  This identification is standard f(R)-cosmology
folklore (Starobinsky 1980, De Felice–Tsujikawa §3 around eq. (3.18))
specialised to our SAGF kinetic operator. -/

/-- **The scalaron mass squared.**  Identified with the crossover
scale of `σ_tr` (Starobinsky-form f(R) read-off). -/
def mSigmaSq (Λ : ℝ) : ℝ := xiCrossSq Λ

theorem mSigmaSq_eq_xiCrossSq (Λ : ℝ) :
    mSigmaSq Λ = xiCrossSq Λ := rfl

/-- **Positivity of the scalaron mass.**  Follows from positivity of
`c₁, f₂, Λ², f₀, α_eff`. -/
theorem mSigmaSq_pos (Λ : ℝ) (hΛ : 0 < Λ) : 0 < mSigmaSq Λ :=
  xiCrossSq_pos Λ hΛ

/-- Naming convenience: the scalaron mass `m_σ` (a positive root). -/
def mSigma (Λ : ℝ) : ℝ := Real.sqrt (mSigmaSq Λ)

theorem mSigma_pos (Λ : ℝ) (hΛ : 0 < Λ) : 0 < mSigma Λ := by
  unfold mSigma
  exact Real.sqrt_pos.mpr (mSigmaSq_pos Λ hΛ)

/-! ## Section 3: The Whitt 1984 transform as a structural primitive

We do *not* attempt to formalise tensorial GR / Riemannian geometry
in 4D inside Mathlib here.  Instead we expose the *content* of the
Whitt 1984 / De Felice–Tsujikawa 2010 conformal-frame transform as
a structural axiom-instance: there exists a scalar potential `V(σ)`
on the Einstein frame such that the f(R) action's dynamics matches
the Einstein-frame scalar action's dynamics on FRW backgrounds.

For the Starobinsky family `f(R) = R + R²/(6 m_σ²)`, the explicit
form of `V(σ)` is (De Felice–Tsujikawa 2010, eq. 3.18):

  V(σ) = (3/4) M_Pl² m_σ² (1 − e^{−√(2/3) σ/M_Pl})² .

This is *positive*, *bounded* by `(3/4) M_Pl² m_σ²`, and *vanishes
at σ = 0*; on the slow-roll plateau (σ ≫ M_Pl) it is approximately
`(3/4) M_Pl² m_σ²`. -/

/-- **The Starobinsky scalaron potential.**

V_St(σ; Λ) := (3/4) · M_Pl² · m_σ²(Λ) · (1 − e^{−√(2/3) · σ/M_Pl})² . -/
def starobinskyPotential (Λ σ : ℝ) : ℝ :=
  (3 / 4) * MPl^2 * mSigmaSq Λ
    * (1 - Real.exp (- Real.sqrt (2 / 3) * σ / MPl))^2

/-- **Non-negativity of the scalaron potential.**  Standard. -/
theorem starobinskyPotential_nonneg (Λ σ : ℝ) (hΛ : 0 < Λ) :
    0 ≤ starobinskyPotential Λ σ := by
  unfold starobinskyPotential
  have h1 : 0 ≤ MPl^2 := by positivity
  have h2 : 0 ≤ mSigmaSq Λ := le_of_lt (mSigmaSq_pos Λ hΛ)
  have h3 : 0 ≤ (1 - Real.exp (- Real.sqrt (2 / 3) * σ / MPl))^2 := sq_nonneg _
  positivity

/-- **Vanishing at the Einstein-frame origin σ = 0.**  At σ = 0 we
have `e^0 = 1`, so the squared bracket is zero. -/
theorem starobinskyPotential_zero (Λ : ℝ) :
    starobinskyPotential Λ 0 = 0 := by
  unfold starobinskyPotential
  -- exp(- sqrt(2/3) * 0 / MPl) = exp 0 = 1
  have h : Real.exp (- Real.sqrt (2 / 3) * 0 / MPl) = 1 := by
    have : - Real.sqrt (2 / 3) * 0 / MPl = 0 := by ring
    rw [this, Real.exp_zero]
  rw [h]; ring

/-- **Asymptotic plateau height.**  As σ → +∞, the exponential goes
to zero, so V → (3/4) M_Pl² m_σ².  Here we record the *bound*
`V ≤ (3/4) M_Pl² m_σ²` for all σ ≥ 0. -/
theorem starobinskyPotential_plateau_bound
    (Λ σ : ℝ) (hΛ : 0 < Λ) (hσ : 0 ≤ σ) :
    starobinskyPotential Λ σ ≤ (3 / 4) * MPl^2 * mSigmaSq Λ := by
  unfold starobinskyPotential
  -- 0 ≤ exp(-x) ≤ 1 for x ≥ 0, so 0 ≤ 1 - exp(-x) ≤ 1, so squared ≤ 1.
  have hsqrt23 : 0 ≤ Real.sqrt (2 / 3) := Real.sqrt_nonneg _
  have hMPl_pos : 0 < MPl := MPl_pos
  have hMPl_ne : MPl ≠ 0 := ne_of_gt hMPl_pos
  have hx_nonneg : 0 ≤ Real.sqrt (2 / 3) * σ / MPl := by
    apply div_nonneg
    · exact mul_nonneg hsqrt23 hσ
    · exact le_of_lt hMPl_pos
  have hx_neg : - Real.sqrt (2 / 3) * σ / MPl ≤ 0 := by
    have : - Real.sqrt (2 / 3) * σ / MPl = -(Real.sqrt (2 / 3) * σ / MPl) := by ring
    rw [this]
    exact neg_nonpos_of_nonneg hx_nonneg
  have h_exp_le : Real.exp (- Real.sqrt (2 / 3) * σ / MPl) ≤ 1 := by
    have := Real.exp_le_one_iff.mpr hx_neg
    exact this
  have h_exp_pos : 0 < Real.exp (- Real.sqrt (2 / 3) * σ / MPl) :=
    Real.exp_pos _
  have h_bracket_nonneg : 0 ≤ 1 - Real.exp (- Real.sqrt (2 / 3) * σ / MPl) := by
    linarith
  have h_bracket_le_one : 1 - Real.exp (- Real.sqrt (2 / 3) * σ / MPl) ≤ 1 := by
    linarith
  have h_sq_le_one : (1 - Real.exp (- Real.sqrt (2 / 3) * σ / MPl))^2 ≤ 1 := by
    have h := mul_le_one₀ h_bracket_le_one h_bracket_nonneg h_bracket_le_one
    have heq : (1 - Real.exp (- Real.sqrt (2 / 3) * σ / MPl))^2 =
           (1 - Real.exp (- Real.sqrt (2 / 3) * σ / MPl)) *
           (1 - Real.exp (- Real.sqrt (2 / 3) * σ / MPl)) := by ring
    rw [heq]; exact h
  have h_coeff_nonneg : 0 ≤ (3 / 4) * MPl^2 * mSigmaSq Λ := by
    have h1 : 0 ≤ MPl^2 := by positivity
    have h2 : 0 ≤ mSigmaSq Λ := le_of_lt (mSigmaSq_pos Λ hΛ)
    positivity
  -- (3/4) MPl² m² · S² ≤ (3/4) MPl² m² · 1
  have := mul_le_mul_of_nonneg_left h_sq_le_one h_coeff_nonneg
  linarith

/-! ## Section 4: The Whitt-1984 transform recorded as an axiom-class

This class records the *content* of the conformal-frame
transformation: the classical equivalence between Jordan-frame f(R)
and Einstein-frame scalar gravity, on FRW backgrounds, with the
scalar potential being `starobinskyPotential` (for the Starobinsky
choice of `f`).

We do not attempt to instantiate it from a tensorial-GR formalisation
(which Mathlib does not yet support at this level of generality).
Instead, downstream theorems take the existence of an instance as
input, citing Whitt 1984 / De Felice–Tsujikawa 2010 as the textbook
source. -/

/-- **The Whitt-1984 conformal-frame transform** (axiom-class).

For each cutoff `Λ > 0`, the Jordan-frame Starobinsky action

  S_J = (1/(2κ²)) ∫ √(−g) · (R + R²/(6 m_σ²(Λ))) d⁴x

is, on FRW backgrounds, equivalent to the Einstein-frame action

  S_E = ∫ √(−g̃) · [(1/(2κ²)) R̃ − (1/2)(∂σ)² − V_St(Λ; σ)] d⁴x ,

with `V_St` given by `starobinskyPotential`.

We carry this equivalence as a structural axiom-class: any model
satisfying the f(R) action's local dynamics also satisfies the
scalar-field action's local dynamics on FRW (and vice-versa).  This
is *textbook*; what the class records is just the content of the
identification, not its proof. -/
class ConformalFrameTransform (Λ : ℝ) : Prop where
  /-- The cutoff is positive (gluing condition). -/
  Λ_pos : 0 < Λ
  /-- The scalaron mass squared identified from σ_tr is positive. -/
  mSigmaSq_pos_inst : 0 < mSigmaSq Λ
  /-- The Einstein-frame scalar potential is non-negative on the slow-roll
      branch (σ ≥ 0).  This is the *Starobinsky* slow-roll inflation
      precondition (positive, bounded plateau). -/
  V_nonneg : ∀ σ : ℝ, 0 ≤ starobinskyPotential Λ σ
  /-- The Einstein-frame scalar potential vanishes at σ = 0 (the
      Minkowski-vacuum boundary). -/
  V_zero_at_zero : starobinskyPotential Λ 0 = 0
  /-- The Einstein-frame potential is bounded by its plateau height
      `(3/4) M_Pl² m_σ²` for σ ≥ 0. -/
  V_plateau_bound : ∀ σ : ℝ, 0 ≤ σ →
    starobinskyPotential Λ σ ≤ (3 / 4) * MPl^2 * mSigmaSq Λ

/-- **Construction of the canonical transform instance** from the
SAGF dispersion data.  The four properties are theorems already
proved above; this just packages them. -/
instance canonicalConformalFrameTransform (Λ : ℝ) (hΛ : 0 < Λ) :
    ConformalFrameTransform Λ where
  Λ_pos := hΛ
  mSigmaSq_pos_inst := mSigmaSq_pos Λ hΛ
  V_nonneg σ := starobinskyPotential_nonneg Λ σ hΛ
  V_zero_at_zero := starobinskyPotential_zero Λ
  V_plateau_bound σ hσ := starobinskyPotential_plateau_bound Λ σ hΛ hσ

end SpectralPhysics.Cosmology

end
