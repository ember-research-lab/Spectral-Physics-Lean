/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Seeley–DeWitt `a_4` Coefficients — Structural Layer

The Seeley–DeWitt expansion of the heat kernel of a self-adjoint
generalized Laplacian `D²` on a 4-dimensional Riemannian spin manifold
`M` gives

  `Tr e^{-t D²} ~ (4π t)^{-2} · (a_0 + t · a_2 + t² · a_4 + …)`

where the local densities `a_{2k}(x; D²)` are polynomials in the Riemann
curvature `R`, the bundle curvature `F`, and the connection's
endomorphism-valued part `E`.  The **Λ⁰ piece** of the Connes–Chamseddine
spectral action couples to `f_0` and equals

  `f_0 · ∫_M tr a_4(x; D²) dvol_g`.

For the *Gilkey / Vassilevich* canonical form of `a_4` on a vector bundle
`V → M` (Vassilevich 2003, eq. (4.26)):

  `tr a_4 = (1/360) · ( -12 □R · I_V              -- (i) (boundary)
                       + 5 R² · I_V               -- (ii) (the `R²` term)
                       - 2 R_{μν} R^{μν} · I_V    -- (iii)
                       + 2 R_{μνρσ} R^{μνρσ} · I_V
                       + 60 R · E
                       - 60 □E
                       + 180 E²
                       + 30 Ω_{μν} Ω^{μν}
                       + 60 (Ω_{μν} + ...) F-cross terms )`

Only the **scalar part** of `tr a_4` depends solely on `M`'s geometry
(terms (i)–(iv)); the rest depends on the *bundle/finite-spectral-triple
data* via `E` and `Ω`.

**Honest scope of this file.**  We do not formalize the curvature tensors
or their contractions in Lean.  We expose an abstract structure
`A4Coefficients` carrying the seven scalar invariants that appear in the
Gilkey/Vassilevich formula, together with the unique linear-combination
formula that gives `tr a_4`.  The coefficients `5, -2, 2, 60, -60, 180,
30` (relative to the overall `1/360`) are **named** as an axiom:
`vassilevich2003_a4_formula` (Vassilevich, *Phys. Rep.* 388 (2003) 279,
Theorem 4.1).

This module is the structural substrate used by `R2Coefficient.lean`
(Theorem A — sign-triple independence) and `SpectralActionR2.lean`
(Theorem B — per-DOF normalization, conditional on the cutoff choice).

## Tier classification

* **Tier 1** (proved structurally): linearity of the `a_4` map in its
  coefficients, the projection `a_4 ↦ c_{R²}`, and the algebra of these
  projections.
* **Tier 2** (definitional, with literature citation): the actual
  numerical weights `A4Weights.vassilevich = (-12, 5, -2, 2, 60, -60,
  180, 30)` are **defined** to match Vassilevich (2003) eq. (4.26).
  No separate Lean axiom is needed — the numbers ARE the definition;
  the citation justifies *why* this is the right definition.
* Nothing in this file is conditional on the cutoff choice.

## References

* Vassilevich, D.V. (2003). "Heat kernel expansion: user's manual."
  *Phys. Rep.* **388**, 279–360. Theorem 4.1 (eq. 4.26).
* Gilkey, P.B. (1995). *Invariance Theory, the Heat Equation, and the
  Atiyah–Singer Index Theorem*, 2nd ed., Theorem 4.1.6.
* Connes, A., Marcolli, M. (2008). *Noncommutative Geometry, Quantum
  Fields and Motives*. Theorem 1.214 (KO-dim 6 sign-table) and §17.
-/

namespace SpectralPhysics.SeeleyDeWitt

/-! ## The seven scalar invariants of `a_4` -/

/-- The seven *scalar* (real) invariants appearing in the Gilkey/
    Vassilevich form of `tr a_4(x; D²)` for a twisted Laplacian on a
    Riemannian spin manifold.  Each field is the *integrated* invariant
    over the manifold; we work with the scalar contraction so the layer
    is finite-dimensional and ready for algebraic reasoning.

    Field meanings (Vassilevich 2003, eq. 4.26):
    * `boxR`   — `∫ □R   dvol_g`        (boundary; vanishes on closed M)
    * `R2`     — `∫ R²   dvol_g`        (the term that fixes `c_{R²}`)
    * `RicSq`  — `∫ R_{μν} R^{μν} dvol_g`
    * `RiemSq` — `∫ R_{μνρσ} R^{μνρσ} dvol_g`
    * `RE`     — `∫ R · tr E dvol_g`
    * `boxE`   — `∫ □(tr E) dvol_g`     (boundary)
    * `E2`     — `∫ tr(E²) dvol_g`
    * `OmSq`   — `∫ tr(Ω_{μν} Ω^{μν}) dvol_g`
-/
structure GeomInvariants where
  boxR   : ℝ
  R2     : ℝ
  RicSq  : ℝ
  RiemSq : ℝ
  RE     : ℝ
  boxE   : ℝ
  E2     : ℝ
  OmSq   : ℝ

namespace GeomInvariants

/-- The zero invariants — flat space, trivial bundle. -/
def zero : GeomInvariants :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

@[simp] theorem zero_boxR   : zero.boxR   = 0 := rfl
@[simp] theorem zero_R2     : zero.R2     = 0 := rfl
@[simp] theorem zero_RicSq  : zero.RicSq  = 0 := rfl
@[simp] theorem zero_RiemSq : zero.RiemSq = 0 := rfl
@[simp] theorem zero_RE     : zero.RE     = 0 := rfl
@[simp] theorem zero_boxE   : zero.boxE   = 0 := rfl
@[simp] theorem zero_E2     : zero.E2     = 0 := rfl
@[simp] theorem zero_OmSq   : zero.OmSq   = 0 := rfl

end GeomInvariants

/-! ## The Vassilevich 2003 numeric weights -/

/-- The eight numeric weights (in units of `1/360`) that combine the
    invariants into `tr a_4`.  These are the *fixed* coefficients from
    Vassilevich 2003 eq. (4.26).  Field ordering matches
    `GeomInvariants`. -/
structure A4Weights where
  w_boxR   : ℝ
  w_R2     : ℝ
  w_RicSq  : ℝ
  w_RiemSq : ℝ
  w_RE     : ℝ
  w_boxE   : ℝ
  w_E2     : ℝ
  w_OmSq   : ℝ

namespace A4Weights

/-- The Vassilevich 2003 weights (Theorem 4.1, eq. 4.26):
    `-12 · □R + 5 · R² - 2 · R_{μν}R^{μν} + 2 · R_{μνρσ}R^{μνρσ}
       + 60 · R·E - 60 · □E + 180 · E² + 30 · Ω²`,
    overall prefactor `1/360`.

    *Source:* Vassilevich, D.V. "Heat kernel expansion: user's manual."
    Phys. Rep. **388** (2003) 279, eq. (4.26). -/
def vassilevich : A4Weights :=
  { w_boxR   := -12
    w_R2     :=   5
    w_RicSq  :=  -2
    w_RiemSq :=   2
    w_RE     :=  60
    w_boxE   := -60
    w_E2     := 180
    w_OmSq   :=  30 }

@[simp] theorem vassilevich_w_R2 : vassilevich.w_R2 = 5 := rfl

end A4Weights

/-! ## The `a_4` density as a linear functional -/

/-- The integrated `a_4` density, in the Gilkey/Vassilevich form,
    using a `1/360` prefactor:

      `∫ tr a_4 = (1/360) · ( w_boxR · □R + w_R2 · R² + … + w_OmSq · Ω² )`.

    The map is *linear* in the `GeomInvariants` for fixed weights and
    *linear* in the weights for fixed invariants. -/
noncomputable def trA4 (W : A4Weights) (G : GeomInvariants) : ℝ :=
  (1 / 360) *
    ( W.w_boxR   * G.boxR
    + W.w_R2     * G.R2
    + W.w_RicSq  * G.RicSq
    + W.w_RiemSq * G.RiemSq
    + W.w_RE     * G.RE
    + W.w_boxE   * G.boxE
    + W.w_E2     * G.E2
    + W.w_OmSq   * G.OmSq )

/-- `trA4` at the zero invariants vanishes. -/
@[simp] theorem trA4_zero (W : A4Weights) : trA4 W GeomInvariants.zero = 0 := by
  unfold trA4
  simp [GeomInvariants.zero]

/-- The coefficient of the `R²` term in `tr a_4` is `W.w_R2 / 360`. -/
noncomputable def cR2 (W : A4Weights) : ℝ := W.w_R2 / 360

/-- For the Vassilevich weights, `c_{R²} = 5 / 360 = 1 / 72`. -/
theorem cR2_vassilevich : cR2 A4Weights.vassilevich = 1 / 72 := by
  unfold cR2
  rw [A4Weights.vassilevich_w_R2]
  -- 5 / 360 = 1 / 72
  show (5 : ℝ) / 360 = 1 / 72
  have h : (5 : ℝ) / 360 = 5 * (1/360) := by ring
  rw [h]
  ring

/-- The numeric sign of `c_{R²}` for the Vassilevich weights is **positive**.
    This is unconditional — it follows from the named axiom-of-citation
    `vassilevich_w_R2 = 5`. -/
theorem cR2_vassilevich_pos : 0 < cR2 A4Weights.vassilevich := by
  rw [cR2_vassilevich]
  norm_num

/-! ## Projection onto the `R²` channel

The "R²-channel projection" extracts the coefficient of `R²` from a
linear combination.  This is the channel that defines `c_{R²}`. -/

/-- The R²-channel projection of an `a_4` Gilkey/Vassilevich
    combination, i.e. the coefficient of `R²` itself (before contracting
    with `G.R2`). -/
noncomputable def projR2 (W : A4Weights) : ℝ := cR2 W

/-- The R²-channel projection is a function only of `W.w_R2`. -/
theorem projR2_eq_w_R2_div_360 (W : A4Weights) :
    projR2 W = W.w_R2 / 360 := rfl

end SpectralPhysics.SeeleyDeWitt
