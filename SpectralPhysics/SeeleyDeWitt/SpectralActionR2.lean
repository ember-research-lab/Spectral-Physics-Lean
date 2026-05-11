/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SeeleyDeWitt.R2Coefficient

/-!
# Theorem B — Per-DOF Normalization of the `R²` Coefficient
## (Conditional on a Cutoff-Function Normalization Choice)

The Connes–Chamseddine spectral action

  `S_CC(D, Λ, f) = Tr f(D²/Λ²)`

depends on a *cutoff function* `f : ℝ → ℝ` only through three moments

  `f_0 = ∫_0^∞ f(u) u^{-1} du,   f_2 = ∫_0^∞ f(u) du,   f_4 = ∫_0^∞ f(u) u du`.

The `Λ⁰` (i.e. `a_4`-multiplied) term of the heat-kernel expansion is

  `f_0 · ∫_M tr a_4 dvol_g`.

Inside `tr a_4`, the **`R²` invariant** has a fixed geometric weight
`5/360 · dim(H_F) = (5/360) · 384 = 16/3` for the framework's
`dim(H_F) = 384` (cf. `SelfModelDeficit.lean`, `Cosmology/Predictions.lean`).
We split `dim(H_F) = 96` (visible, Standard-Model) `+ 288` (hidden /
"dark"), and ask: what does the *per-hidden-DOF* spectral-action
coefficient of `R²` look like?

The numerical claim "`c_{R²}^{per-hidden-DOF} = 1/288`" is exactly the
content of choosing the cutoff function `f_0` so that the
**bare** spectral-action coefficient `f_0 · 5/360 · 384` normalizes to
exactly `1`.  With that convention,

  `c_{R²}^{per-hidden-DOF} := c_{R²} / dim(hidden) = 1 / 288`.

This is a **conventional identity** — it follows immediately once you
*choose* `f_0` to set the prefactor to unity, multiplied by the
group-theoretic fact `dim(hidden) = 288`.

## Honest scope

* The theorem **explicitly conditions** on the cutoff normalization
  choice via a hypothesis `CutoffNormalization`.
* It does **not** claim that the cutoff choice itself is forced by the
  theory.  In particular, the prior `cutoff_rescaling_per_dof` axiom
  (which silently chose `f_0` to make `c_{R²}` equal `1`) is removed.
* Positivity / nonzero-ness of `c_{R²}` is **not** consumed from the
  cutoff choice.  The geometric `c_{R²} = 5/360 > 0` from Theorem A
  is reused — making the cutoff-induced normalization a *rescaling*
  rather than a positivity claim.

## Why this matters (audit response)

The prior `compute/R2-sign` branch packaged Theorem A and Theorem B as
a single derivation, with a hidden axiom `cutoff_rescaling_per_dof`
choosing `f_0` so that `c_{R²} = 1`.  Under that axiom, the headline
"`c_{R²} > 0` ∧ `c_{R²}/288 = 1/288`" was trivial.  The adversarial
audit caught this conflation.  This file formalizes the **separated**
Theorem B as a *cutoff-conditional* result, with no hidden axiom.

## References

* Chamseddine, A.H., Connes, A. (1996). "The spectral action principle."
  *Comm. Math. Phys.* **186**, 731. (Cutoff-moment structure of `S_CC`.)
* Connes, A., Marcolli, M. (2008). *Noncommutative Geometry, Quantum
  Fields and Motives*. §17.
-/

namespace SpectralPhysics.SeeleyDeWitt

/-! ## Hidden-sector dimension -/

/-- The framework's hidden-sector dimension: `dim(hidden) = 288`
    (`384 = dim(H_F) = 96 + 288`, cf. `Cosmology/Predictions.lean`). -/
def dim_hidden : ℕ := 288

@[simp] theorem dim_hidden_eq : dim_hidden = 288 := rfl

/-- The hidden-sector dimension as a real number, with a name to
    prevent inadvertent coercion confusion. -/
noncomputable def dim_hidden_R : ℝ := (dim_hidden : ℝ)

@[simp] theorem dim_hidden_R_eq : dim_hidden_R = 288 := by
  unfold dim_hidden_R
  rw [dim_hidden_eq]
  norm_num

/-- `dim_hidden` is nonzero. -/
theorem dim_hidden_R_ne_zero : dim_hidden_R ≠ 0 := by
  rw [dim_hidden_R_eq]
  norm_num

/-! ## Cutoff function moments and the normalization choice -/

/-- The Connes–Chamseddine cutoff-function moments.  We only carry the
    one moment relevant for the `Λ⁰ = a_4` term, namely `f_0`. -/
structure CutoffMoments where
  /-- `f_0 = ∫_0^∞ f(u) u^{-1} du`. -/
  f_0 : ℝ
  /-- Positivity. -/
  f_0_pos : 0 < f_0

namespace CutoffMoments

/-- The spectral-action multiplier of the geometric `R²` coefficient
    `c_{R²} = 1/72` is `f_0 · c_{R²} = f_0 / 72`. -/
noncomputable def spectralActionR2 (m : CutoffMoments) : ℝ :=
  m.f_0 * cR2 A4Weights.vassilevich

/-- For positive `f_0`, the spectral-action `R²` multiplier is positive. -/
theorem spectralActionR2_pos (m : CutoffMoments) :
    0 < m.spectralActionR2 := by
  unfold spectralActionR2
  exact mul_pos m.f_0_pos cR2_vassilevich_pos

end CutoffMoments

/-! ## The cutoff normalization choice — the conditional hypothesis -/

/-- **Cutoff normalization choice.**  A cutoff-moment specification is
    *normalized* if the bare spectral-action coefficient of `R²` is
    chosen to equal exactly `1`:

      `f_0 · cR2 A4Weights.vassilevich = 1`.

    This corresponds to the prior branch's `cutoff_rescaling_per_dof`,
    now stated as an *explicit hypothesis* rather than a hidden axiom.
    Equivalent forms: `f_0 = 72`, or
    `m.spectralActionR2 = 1` (using `CutoffMoments.spectralActionR2`). -/
def CutoffNormalization (m : CutoffMoments) : Prop :=
  m.spectralActionR2 = 1

/-- **Solving for the normalized cutoff.**  The cutoff-normalization
    condition picks a *unique* value of `f_0`: `f_0 = 72`.
    (Because `f_0 · (1/72) = 1`.) -/
theorem cutoff_normalization_solves_f0 (m : CutoffMoments)
    (h : CutoffNormalization m) :
    m.f_0 = 72 := by
  -- f_0 · (1/72) = 1   ⇒   f_0 = 72
  unfold CutoffNormalization CutoffMoments.spectralActionR2 at h
  rw [cR2_vassilevich] at h
  -- h : m.f_0 * (1/72) = 1
  linarith

/-- **Conversely**, if `f_0 = 72`, the cutoff normalization holds. -/
theorem cutoff_normalization_of_f0_seventytwo (m : CutoffMoments)
    (h : m.f_0 = 72) :
    CutoffNormalization m := by
  unfold CutoffNormalization CutoffMoments.spectralActionR2
  rw [cR2_vassilevich, h]
  norm_num

/-! ## Theorem B — Per-DOF normalization (conditional) -/

/-- The "per-hidden-DOF" spectral-action `R²` coefficient is the
    spectral-action `R²` coefficient divided by `dim(hidden) = 288`.

    This is the framework's headline normalization: dividing the
    spectral-action `Λ⁰` term (which carries the bare `R²` coefficient)
    by the hidden-sector dimension. -/
noncomputable def c_R2_per_hidden_DOF (m : CutoffMoments) : ℝ :=
  m.spectralActionR2 / dim_hidden_R

/-- **Theorem B (CONDITIONAL).**  *If* the cutoff function `f` is chosen
    so that the bare spectral-action coefficient of `R²` equals `1` —
    i.e. `CutoffNormalization m` — *then* the per-hidden-DOF `R²`
    coefficient equals exactly `1 / 288`.

    **This is a conventional identity**, not a derivation:
    `c_{R²}/dim(hidden) = 1/dim(hidden)` follows tautologically from
    *defining* the normalization so that `c_{R²} := 1`.

    The point of the theorem is to make the conditional structure
    **explicit** so no axiom hides the cutoff choice.

    Compare with **Theorem A** (`r2_sign_independent_of_sign_triple`)
    which is unconditional: there the *sign* and the *value* `1/72` are
    geometric facts independent of the cutoff. -/
theorem r2_per_dof_normalized (m : CutoffMoments)
    (h_cutoff : CutoffNormalization m) :
    c_R2_per_hidden_DOF m = 1 / dim_hidden_R := by
  unfold c_R2_per_hidden_DOF
  unfold CutoffNormalization at h_cutoff
  -- h_cutoff : m.spectralActionR2 = 1
  rw [h_cutoff]

/-- **Theorem B — numerical specialization.**  Under the cutoff
    normalization, `c_{R²}^{per-hidden-DOF} = 1/288` — exactly the
    framework's headline ratio.  Again: this is a *consequence of the
    normalization choice*, not a derivation. -/
theorem r2_per_dof_eq_one_over_288 (m : CutoffMoments)
    (h_cutoff : CutoffNormalization m) :
    c_R2_per_hidden_DOF m = 1 / 288 := by
  rw [r2_per_dof_normalized m h_cutoff, dim_hidden_R_eq]

/-! ## Anti-claim: WITHOUT the cutoff normalization, the per-DOF
    coefficient depends on `f_0` -/

/-- **Anti-claim (the audit's substantive point).**  If we do *not*
    impose `CutoffNormalization`, the per-hidden-DOF `R²` coefficient
    is just `f_0 / (72 · 288) = f_0 / 20736`, a function of the
    cutoff `f_0`.

    There is no universal positive value forced by the geometry alone:
    the *positivity* comes from Theorem A's `cR2 > 0` plus `f_0 > 0`,
    but the **numerical value** is entirely a cutoff-convention.

    This makes precise what the prior `cutoff_rescaling_per_dof` axiom
    was hiding. -/
theorem c_R2_per_hidden_DOF_value (m : CutoffMoments) :
    c_R2_per_hidden_DOF m = m.f_0 / 20736 := by
  unfold c_R2_per_hidden_DOF CutoffMoments.spectralActionR2
  rw [cR2_vassilevich, dim_hidden_R_eq]
  field_simp
  ring

/-- **Cutoff-free statement: positivity holds.**  Whatever positive
    cutoff is chosen, the per-hidden-DOF coefficient is positive.  This
    is the most we can say *without* picking a normalization, and it
    is *strictly weaker* than the `= 1/288` claim. -/
theorem c_R2_per_hidden_DOF_pos (m : CutoffMoments) :
    0 < c_R2_per_hidden_DOF m := by
  rw [c_R2_per_hidden_DOF_value]
  have h := m.f_0_pos
  -- f_0 > 0 and 20736 > 0 ⇒ f_0/20736 > 0
  exact div_pos h (by norm_num)

/-! ## Comparison: Theorem A (universal) vs Theorem B (conditional)

| Claim                                  | Theorem A           | Theorem B            |
|----------------------------------------|---------------------|----------------------|
| Sign of `c_{R²}`                       | `+` unconditional   | reused from A        |
| Numerical value of `c_{R²}`            | `5/360 = 1/72`      | depends on `f_0`     |
| `c_{R²}` invariant under sign triple   | YES — by structure  | inherited from A     |
| Per-DOF ratio `c/dim(hidden) = 1/288`  | NOT made            | YES, **iff** `f_0 = 72`  |

What the prior branch did wrong: it stated the per-DOF ratio as
*unconditional*.  This file makes the conditioning explicit. -/

end SpectralPhysics.SeeleyDeWitt
