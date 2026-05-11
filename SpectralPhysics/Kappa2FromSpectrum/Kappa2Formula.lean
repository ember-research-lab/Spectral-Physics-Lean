/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Kappa2FromSpectrum.DFSpectrum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The κ₂ cumulant from the full singular-value spectrum

v0.9 Proposition `prop:faith-tower` (line 9735) defines

  `κ₂ = Var(-log y_f)`

over the visible-sector spectral distribution.  v0.9 line 9747
upgrades this to the **full singular-value spectrum** reading: the
variance is computed over **all 192 singular values of `M`** on the
half-space `H_L`, not over the 48 visible Yukawas alone.

In that reading, the cumulant is the multiplicity-weighted population
variance

  `κ₂_full = (1/192) · [144 · (ξ_hid - μ)² + Σ_f mult_f · (ξ_f - μ)²]`,

where the mean is

  `μ_full = (1/192) · [144 · ξ_hid + Σ_f mult_f · ξ_f]`.

This file states the formula structurally as a definition over a
`FullDFSpectrum`.  No numerical evaluation happens here; the bracket
appears in `Bracket.lean`.

## Audit-discipline classification

* **Tier 1** (proved here): the formula is a *definition*, not an
  axiom.  All arithmetic identities downstream of it (positivity,
  expansion forms) are proved unconditionally over `FullDFSpectrum`.
* **Tier 2** (no new axioms): the empirical content lives in the
  hypothesis `T : FullDFSpectrum` and was already named in
  `DFSpectrum.lean`.

## Anti-pattern check

This file deliberately does **not** define `κ₂ := 258`.  The integer
that emerges downstream (in `Bracket.lean`) does so through a
computation chain consuming the named-axiom inputs.  If any named
axiom is removed, the bracket fails to construct.
-/

namespace SpectralPhysics.Kappa2FromSpectrum

open Real

/-! ## The unweighted sum and mean over the 12 distinct Yukawa labels -/

/-- Multiplicity-weighted sum of visible depths
    `Σ_f mult_f · ξ_f` (units: dimensionless).  Closed-form sum over
    the 12 fermion labels. -/
noncomputable def visibleDepthSum (T : FullDFSpectrum) : ℝ :=
  (Fermion.multOf .top : ℝ)     * T.xiVisible .top
  + (Fermion.multOf .charm : ℝ)   * T.xiVisible .charm
  + (Fermion.multOf .up : ℝ)      * T.xiVisible .up
  + (Fermion.multOf .bottom : ℝ)  * T.xiVisible .bottom
  + (Fermion.multOf .strange : ℝ) * T.xiVisible .strange
  + (Fermion.multOf .down : ℝ)    * T.xiVisible .down
  + (Fermion.multOf .tau : ℝ)     * T.xiVisible .tau
  + (Fermion.multOf .mu : ℝ)      * T.xiVisible .mu
  + (Fermion.multOf .el : ℝ)      * T.xiVisible .el
  + (Fermion.multOf .nu1 : ℝ)     * T.xiVisible .nu1
  + (Fermion.multOf .nu2 : ℝ)     * T.xiVisible .nu2
  + (Fermion.multOf .nu3 : ℝ)     * T.xiVisible .nu3

/-- Multiplicity-weighted sum of squared visible depths
    `Σ_f mult_f · ξ_f²`. -/
noncomputable def visibleDepthSqSum (T : FullDFSpectrum) : ℝ :=
  (Fermion.multOf .top : ℝ)     * (T.xiVisible .top) ^ 2
  + (Fermion.multOf .charm : ℝ)   * (T.xiVisible .charm) ^ 2
  + (Fermion.multOf .up : ℝ)      * (T.xiVisible .up) ^ 2
  + (Fermion.multOf .bottom : ℝ)  * (T.xiVisible .bottom) ^ 2
  + (Fermion.multOf .strange : ℝ) * (T.xiVisible .strange) ^ 2
  + (Fermion.multOf .down : ℝ)    * (T.xiVisible .down) ^ 2
  + (Fermion.multOf .tau : ℝ)     * (T.xiVisible .tau) ^ 2
  + (Fermion.multOf .mu : ℝ)      * (T.xiVisible .mu) ^ 2
  + (Fermion.multOf .el : ℝ)      * (T.xiVisible .el) ^ 2
  + (Fermion.multOf .nu1 : ℝ)     * (T.xiVisible .nu1) ^ 2
  + (Fermion.multOf .nu2 : ℝ)     * (T.xiVisible .nu2) ^ 2
  + (Fermion.multOf .nu3 : ℝ)     * (T.xiVisible .nu3) ^ 2

/-! ## Full-spectrum first and second moments -/

/-- First moment over the full 192-singular-value spectrum:
    `μ_full = (144 · ξ_hid + Σ_f mult_f · ξ_f) / 192`. -/
noncomputable def fullMean (T : FullDFSpectrum) : ℝ :=
  (144 * T.xiHidden + visibleDepthSum T) / 192

/-- Raw (uncentred) second moment over the full spectrum:
    `m₂_full = (144 · ξ_hid² + Σ_f mult_f · ξ_f²) / 192`. -/
noncomputable def fullRawSecondMoment (T : FullDFSpectrum) : ℝ :=
  (144 * T.xiHidden ^ 2 + visibleDepthSqSum T) / 192

/-- The κ₂ cumulant computed from the full singular-value spectrum,
    as the *population variance* `m₂ - μ²`:
    `κ₂_full = E[ξ²] − E[ξ]²`. -/
noncomputable def kappa2Full (T : FullDFSpectrum) : ℝ :=
  fullRawSecondMoment T - (fullMean T) ^ 2

/-! ## Alternate (equivalent) form: the explicit deviation-squared
    sum.  Useful for downstream analysis. -/

/-- Centred second moment, summed multiplicity-weighted, divided by 192:
    `(1/192) [144 · (ξ_hid - μ)² + Σ_f mult_f · (ξ_f - μ)²]`. -/
noncomputable def kappa2FullCentred (T : FullDFSpectrum) : ℝ :=
  ( 144 * (T.xiHidden - fullMean T) ^ 2
    + (Fermion.multOf .top : ℝ)     * (T.xiVisible .top   - fullMean T) ^ 2
    + (Fermion.multOf .charm : ℝ)   * (T.xiVisible .charm - fullMean T) ^ 2
    + (Fermion.multOf .up : ℝ)      * (T.xiVisible .up    - fullMean T) ^ 2
    + (Fermion.multOf .bottom : ℝ)  * (T.xiVisible .bottom - fullMean T) ^ 2
    + (Fermion.multOf .strange : ℝ) * (T.xiVisible .strange - fullMean T) ^ 2
    + (Fermion.multOf .down : ℝ)    * (T.xiVisible .down  - fullMean T) ^ 2
    + (Fermion.multOf .tau : ℝ)     * (T.xiVisible .tau   - fullMean T) ^ 2
    + (Fermion.multOf .mu : ℝ)      * (T.xiVisible .mu    - fullMean T) ^ 2
    + (Fermion.multOf .el : ℝ)      * (T.xiVisible .el    - fullMean T) ^ 2
    + (Fermion.multOf .nu1 : ℝ)     * (T.xiVisible .nu1   - fullMean T) ^ 2
    + (Fermion.multOf .nu2 : ℝ)     * (T.xiVisible .nu2   - fullMean T) ^ 2
    + (Fermion.multOf .nu3 : ℝ)     * (T.xiVisible .nu3   - fullMean T) ^ 2 ) / 192

/-- Equivalence of the two cumulant formulae: variance equals
    `E[ξ²] − E[ξ]²`.  Proved by `ring` after expanding the squares,
    using `144 + sum_multOf = 192`. -/
theorem kappa2Full_eq_centred (T : FullDFSpectrum) :
    kappa2Full T = kappa2FullCentred T := by
  unfold kappa2Full kappa2FullCentred fullRawSecondMoment
         fullMean visibleDepthSum visibleDepthSqSum
  -- Numeric form: 192 = 144 + (6·6 + 2·6) -- but unfolding multOf for each f
  -- The identity `Var(X) = E(X²) - E(X)²` holds for any finite weighted measure;
  -- here the weights are 144, 6 (six times), 2 (six times) summing to 192.
  -- We unfold multOf and ring.
  simp [Fermion.multOf]
  ring

/-! ## Basic positivity -/

/-- `κ₂_full ≥ 0`: variance of any real random variable is non-negative.
    Proved by using the centred form, which is a sum of non-negative
    weighted squares divided by a positive denominator. -/
theorem kappa2Full_nonneg (T : FullDFSpectrum) : 0 ≤ kappa2Full T := by
  rw [kappa2Full_eq_centred]
  unfold kappa2FullCentred
  have h₁ : (0 : ℝ) < 192 := by norm_num
  apply div_nonneg _ (le_of_lt h₁)
  -- Sum of 13 weighted squares is nonneg
  have sq_nn : ∀ x : ℝ, 0 ≤ x ^ 2 := fun x => sq_nonneg x
  have w_hid : (0 : ℝ) ≤ 144 := by norm_num
  have w_six : (0 : ℝ) ≤ ((6 : ℕ) : ℝ) := by norm_num
  have w_two : (0 : ℝ) ≤ ((2 : ℕ) : ℝ) := by norm_num
  -- Simplify each multiplicity cast
  simp only [Fermion.multOf, Nat.cast_ofNat]
  positivity

end SpectralPhysics.Kappa2FromSpectrum
