/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SeeleyDeWitt.A4Coefficients
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# GraphDirac — operator-specific `a₄` curvature coefficients (scalar, spin Dirac, graph Dirac)

`A4Weights.vassilevich` holds the *general* Gilkey/Vassilevich weights of `∫ tr a₄` for a
Laplace-type operator `∇*∇ − E` with bundle curvature `Ω`. `cR2` reads only the bare `R²` weight
(`5/360 = 1/72`). The total `R²`, `|Ric|²`, `|Riem|²` coefficients of a *given* operator also
receive contributions from `R·tr E`, `tr E²` and `tr Ω²`, which depend on the operator. This file
performs that substitution for four operators and proves the resulting coefficients:

* minimal scalar Laplacian (`E = 0`, `Ω = 0`, rank 1): `(5, −2, 2)/360`;
* spin Dirac square (Lichnerowicz `E = −R/4`, spin curvature, rank 4): `(5, −8, −7)/360`,
  i.e. `(−18 C² + 11 E)/360` — no `R²` term, negative Weyl² term;
* Hodge Laplacian on 1-forms (Weitzenböck `E = −Ric`, rank 4): `(−40, 172, −22)/360`;
* graph Dirac `d + d*` on vertices ⊕ edges, continuum `Λ⁰ ⊕ Λ¹` (the SAGF operator adopted in the
  manuscript on 2026-09-22, `rem:graph-dirac-adoption`): `(−35, 170, −20)/360`.

**Inputs (not proved here):** the per-operator trace identities `tr E`, `tr E²`, `tr Ω_{ij}Ω_{ij}`
(standard; e.g. `tr Ω² = −½|Riem|²` for the spin connection on rank-4 spinors). The *assembly*
is proved. The resulting vectors were also confirmed on exact spectra of `S⁴`, `S²×S²`, `S³×S¹`,
`S²×T²`, `T⁴` (free fit, residual `< 10⁻¹⁸`; independent verifier DERIVED ×3 routes), see
`~/ember-tasks/weyl-sign-sagf-2026-09-22/` in the lab workspace.

Main results: `eff_spinDirac`, `eff_graphDirac`, `rTwo_spinDirac` (`= 0`),
`rTwo_graphDirac` (`= 15`, i.e. `α_tr = 1/24`), `weyl_graphDirac` (`= 45 > 0`),
`alphaEff_graphDirac_neg`, `pointwise_nonneg` (the correct positivity criterion
`β ≥ 0 ∧ α + β/4 ≥ 0`, using `R² ≤ 4|Ric|²`), and `Kf2_invariant` (`32·96 = 64·48`).
-/

noncomputable section

namespace SpectralPhysics.SeeleyDeWitt.GraphDirac

/-- Coefficients of `(R², |Ric|², |Riem|²)` in an integrated curvature-squared density. -/
@[ext] structure Curv3 where
  R2 : ℝ
  Ric : ℝ
  Riem : ℝ

/-- Trace data of a Laplace-type operator `∇*∇ − E` on a bundle of rank `rank`:
`tr E = trE · R`, and `tr E²`, `tr Ω_{ij}Ω_{ij}` expressed in the curvature basis. -/
structure TraceData where
  rank : ℝ
  trE : ℝ
  trE2 : Curv3
  trOm2 : Curv3

/-- Effective curvature weights of `∫ tr a₄` (units of `1/360`, total derivatives dropped) after
substituting `E` and `Ω` into the general weights `W`. The `R·tr E` term contributes to `R²`. -/
def eff (W : A4Weights) (T : TraceData) : Curv3 where
  R2 := T.rank * W.w_R2 + W.w_RE * T.trE + W.w_E2 * T.trE2.R2 + W.w_OmSq * T.trOm2.R2
  Ric := T.rank * W.w_RicSq + W.w_E2 * T.trE2.Ric + W.w_OmSq * T.trOm2.Ric
  Riem := T.rank * W.w_RiemSq + W.w_E2 * T.trE2.Riem + W.w_OmSq * T.trOm2.Riem

/-- Coefficient of `R` in `a₂ = (4π)⁻² ∫ tr(E + R/6)`. Negative ⇔ Newton's constant `G > 0`
(sphere-positive curvature convention, Euclidean action `−∫R/16πG`). -/
def a2 (T : TraceData) : ℝ := T.trE + T.rank / 6

instance : Add Curv3 := ⟨fun a b => ⟨a.R2 + b.R2, a.Ric + b.Ric, a.Riem + b.Riem⟩⟩

@[simp] lemma add_R2 (a b : Curv3) : (a + b).R2 = a.R2 + b.R2 := rfl
@[simp] lemma add_Ric (a b : Curv3) : (a + b).Ric = a.Ric + b.Ric := rfl
@[simp] lemma add_Riem (a b : Curv3) : (a + b).Riem = a.Riem + b.Riem := rfl

/-! ## Trace data (inputs) -/

/-- Minimal scalar Laplacian: `E = 0`, `Ω = 0`, rank 1. -/
def scalar : TraceData := ⟨1, 0, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩⟩

/-- Spin Dirac square: `E = −R/4 · 1₄` (Lichnerowicz), `tr E² = R²/4`,
`tr Ω_{ij}Ω_{ij} = −½|Riem|²`, rank 4. -/
def spinDirac : TraceData := ⟨4, -1, ⟨1 / 4, 0, 0⟩, ⟨0, 0, -1 / 2⟩⟩

/-- Hodge Laplacian on 1-forms: `E = −Ric` (Weitzenböck), `tr E² = |Ric|²`,
`tr Ω_{ij}Ω_{ij} = −|Riem|²`, rank 4. -/
def oneForm : TraceData := ⟨4, -1, ⟨0, 1, 0⟩, ⟨0, 0, -1⟩⟩

/-! ## Effective `a₄` weights -/

open A4Weights in
theorem eff_scalar : eff vassilevich scalar = ⟨5, -2, 2⟩ := by
  ext <;> simp [eff, scalar, vassilevich]

open A4Weights in
theorem eff_spinDirac : eff vassilevich spinDirac = ⟨5, -8, -7⟩ := by
  ext <;> simp [eff, spinDirac, vassilevich] <;> norm_num

open A4Weights in
theorem eff_oneForm : eff vassilevich oneForm = ⟨-40, 172, -22⟩ := by
  ext <;> simp [eff, oneForm, vassilevich] <;> norm_num

open A4Weights in
/-- Graph Dirac `d + d*` on vertices ⊕ edges; continuum `Λ⁰ ⊕ Λ¹`: the sum of the two blocks. -/
theorem eff_graphDirac :
    eff vassilevich scalar + eff vassilevich oneForm = ⟨-35, 170, -20⟩ := by
  rw [eff_scalar, eff_oneForm]; ext <;> simp <;> norm_num

/-! ## Weyl basis: `A R² + B |Ric|² + C |Riem|² = w C² + e E + g R²`

with `C² = |Riem|² − 2|Ric|² + R²/3` (Weyl squared) and `E = |Riem|² − 4|Ric|² + R²` (Euler). -/

/-- Euler coefficient. -/
def eulerCoeff (c : Curv3) : ℝ := -(c.Ric + 2 * c.Riem) / 2
/-- Weyl² coefficient. -/
def weyl (c : Curv3) : ℝ := c.Riem - eulerCoeff c
/-- `R²` coefficient in the Weyl basis = the trace-sector coefficient `α_tr` (×360). -/
def rTwo (c : Curv3) : ℝ := c.R2 - weyl c / 3 - eulerCoeff c

/-- The Weyl-basis decomposition is exact (pointwise identity of quadratic forms). -/
theorem weyl_decomp (c : Curv3) (R2 Ric Riem : ℝ) :
    c.R2 * R2 + c.Ric * Ric + c.Riem * Riem
      = weyl c * (Riem - 2 * Ric + R2 / 3) + eulerCoeff c * (Riem - 4 * Ric + R2)
        + rTwo c * R2 := by
  simp only [weyl, rTwo, eulerCoeff]; ring

/-- Gauss–Bonnet-eliminated couplings (manuscript `prop:eff-couplings`), ×360. -/
def alphaEff (c : Curv3) : ℝ := c.R2 - c.Riem
def betaEff (c : Curv3) : ℝ := c.Ric + 4 * c.Riem

/-- `α_tr = α_eff + β_eff/3` is the Weyl-basis `R²` coefficient. -/
theorem rTwo_eq (c : Curv3) : rTwo c = alphaEff c + betaEff c / 3 := by
  simp only [rTwo, weyl, eulerCoeff, alphaEff, betaEff]; ring

theorem rTwo_scalar : rTwo ⟨5, -2, 2⟩ = 5 := by norm_num [rTwo, weyl, eulerCoeff]
theorem rTwo_spinDirac : rTwo ⟨5, -8, -7⟩ = 0 := by norm_num [rTwo, weyl, eulerCoeff]
theorem rTwo_graphDirac : rTwo ⟨-35, 170, -20⟩ = 15 := by norm_num [rTwo, weyl, eulerCoeff]

theorem weyl_scalar : weyl ⟨5, -2, 2⟩ = 3 := by norm_num [weyl, eulerCoeff]
theorem weyl_spinDirac : weyl ⟨5, -8, -7⟩ = -18 := by norm_num [weyl, eulerCoeff]
theorem weyl_graphDirac : weyl ⟨-35, 170, -20⟩ = 45 := by norm_num [weyl, eulerCoeff]

/-- Under the graph Dirac `α_eff = −15/360 = −1/24 < 0` while `β_eff = 90/360 = 1/4`. -/
theorem alphaEff_graphDirac_neg : alphaEff ⟨-35, 170, -20⟩ = -15 := by norm_num [alphaEff]
theorem betaEff_graphDirac : betaEff ⟨-35, 170, -20⟩ = 90 := by norm_num [betaEff]
/-- `α_* = α_eff + β_eff/4 = 7.5/360 = 1/48 > 0`. -/
theorem alphaStar_graphDirac : alphaEff ⟨-35, 170, -20⟩ + betaEff ⟨-35, 170, -20⟩ / 4 = 15 / 2 := by
  norm_num [alphaEff, betaEff]

/-! ## Newton's constant sign (`a₂`) -/

theorem a2_scalar : a2 scalar = 1 / 6 := by norm_num [a2, scalar]
theorem a2_spinDirac : a2 spinDirac = -1 / 3 := by norm_num [a2, spinDirac]
/-- `Λ⁰ ⊕ Λ¹`: half the spin-Dirac value, same sign (so `M_Pl² = 32 f₂Λ²/π` at fixed `dim H_F`). -/
theorem a2_graphDirac : a2 scalar + a2 oneForm = -1 / 6 := by norm_num [a2, scalar, oneForm]

/-! ## The correct positivity criterion -/

/-- In `d = 4`, `R² ≤ 4|Ric|²` (Cauchy–Schwarz). Given it, `α R² + β |Ric|² ≥ (α + β/4) R²`
whenever `β ≥ 0`. -/
theorem lower_bound (α β R2 Ric : ℝ) (hβ : 0 ≤ β) (hCS : R2 ≤ 4 * Ric) :
    (α + β / 4) * R2 ≤ α * R2 + β * Ric := by
  nlinarith [mul_nonneg hβ (by linarith : (0 : ℝ) ≤ Ric - R2 / 4)]

/-- Pointwise non-negativity of `α R² + β |Ric|²` from `β ≥ 0`, `α + β/4 ≥ 0`
(the criterion `lem:sagf-L2-bound` needs; "both coefficients positive" is not it). -/
theorem pointwise_nonneg (α β R2 Ric : ℝ) (hβ : 0 ≤ β) (hα : 0 ≤ α + β / 4)
    (hR : 0 ≤ R2) (hCS : R2 ≤ 4 * Ric) : 0 ≤ α * R2 + β * Ric :=
  le_trans (mul_nonneg hα hR) (lower_bound α β R2 Ric hβ hCS)

/-! ## Planck-mass normalisation -/

/-- The Planck-mass relation fixes only `K·f₂`: the graph Dirac (`K = 32`) with the visible count
`f₂ = 96 e⁶` reproduces the spin-Dirac (`K = 64`) value with `f₂ = 48 e⁶`. -/
theorem Kf2_invariant : (32 : ℝ) * (96 * Real.exp 6) = 64 * (48 * Real.exp 6) := by ring

end SpectralPhysics.SeeleyDeWitt.GraphDirac

end
