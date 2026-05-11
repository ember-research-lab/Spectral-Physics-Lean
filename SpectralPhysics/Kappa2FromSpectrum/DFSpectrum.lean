/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# The full singular-value spectrum of `D_F` (v0.9 §24 / line 8411)

The finite Dirac operator `D_F` of the spectral-physics framework has the
off-diagonal form
```
  D_F = ⎛  0    M  ⎞
        ⎝ M†   0  ⎠
```
acting on `H_F = H_L ⊕ H_R` with `dim H_L = dim H_R = 192`.
The 192 singular values of `M : H_R → H_L` decompose by v0.9
Proposition `prop:zeta-explicit` (line 8402, eq. 8405) as

* **144 hidden singular values**, all equal to a single scale `M_s`
  (the Majorana mass, equivalently `M_R` in the see-saw mechanism);
* **48 visible singular values**, the SM Yukawa-driven masses
  `m_f = (y_f / √2) · v` with multiplicities
  `mult_q = 6` (color × particle/anti), `mult_ℓ = mult_ν = 2`.

This file encodes that decomposition structurally.  No numerical
Yukawa values are introduced here; they enter as **named axioms** with
PDG citations.  The Hilbert-space dimensions follow the v0.9
`prop:zeta-explicit` decomposition, where `dim H_L = 192` and the
full `H_F = H_L ⊕ H_R` carries the `J`-doubling to 384 = 2 · 192 modes
(matching the `2 · 4 · 8 · 3 · 2` factorisation from
`SelfModelDeficitRigorous/SectorDecomposition.lean`).

## Audit-discipline classification

* **Tier 1** (proved unconditionally here): the structural arithmetic
  identities — `192 = 144 + 48`, `48 = 2 · (9 + 9 + 3 + 3)`, the
  `J`-doubling `384 = 2 · 192`.
* **Tier 2** (named axioms with citations): the PDG-anchored visible
  fermion masses and the v0.9 / SO(10)-see-saw Majorana-mass window
  `M_R ∈ [3·10¹⁴, 1.5·10¹⁵]` GeV.  Each empirical input is one named
  axiom citing a real source (PDG 2024 or v0.9 thm-MR-window).
* **Tier 3** (not here): the operator-algebraic derivation of the
  spectral decomposition itself; that lives in v0.9 §24 and is
  assumed as the *definition* of `D_F`'s spectrum.

## References

* Ben-Shalom, "Spectral Physics", v0.9, §24:
  - Definition `def:half-zeta` (line 8394, eq. 8397).
  - Proposition `prop:zeta-explicit` (line 8402, eq. 8405).
  - Proposition `prop:cc-hidden` (referenced line 8411).
* Particle Data Group, *Review of Particle Physics*, 2024 (Workman
  et al.), chapter 67 (running quark masses).
* Mohapatra & Senjanović 1980 (see-saw mechanism).
-/

namespace SpectralPhysics.Kappa2FromSpectrum

open Real

/-! ## Hilbert-space dimensions -/

/-- Dimension of one `J`-sector of the finite-spectral-triple Hilbert
    space.  v0.9 def `def:half-zeta` (line 8395): `dim H_L = 192`. -/
def dimHL : ℕ := 192

/-- Number of **hidden** singular values of `M`, all equal to `M_s`.
    From v0.9 line 8411: 144 hidden among the 192. -/
def NHidden : ℕ := 144

/-- Number of **visible** singular values of `M` (sum of multiplicities).
    From v0.9 line 8411: `48 = 2 · (9 + 9 + 3 + 3)` — quarks (mult 6
    each, three generations × two flavours = 18+18) plus charged
    leptons (mult 2 × 3 = 6) plus neutrinos (mult 2 × 3 = 6). -/
def NVisible : ℕ := 48

/-- The 144 + 48 = 192 spectral identity (Tier 1, combinatorial). -/
theorem hidden_plus_visible_eq_HL :
    NHidden + NVisible = dimHL := by decide

/-- The visible-mode count factorisation: `48 = 2·(9 + 9 + 3 + 3)`.
    9 = 3 generations × color factor 3 (quarks); 3 = 3 generations
    (leptons, neutrinos); outer 2 = particle/anti. -/
theorem visible_factorisation :
    NVisible = 2 * (9 + 9 + 3 + 3) := by decide

/-- The `J`-doubling: `H_F = H_L ⊕ H_R`, `dim H_F = 2 · 192 = 384`. -/
def dimHF : ℕ := 2 * dimHL

theorem dimHF_eq_384 : dimHF = 384 := by decide

/-! ## Fermion labels and multiplicities -/

/-- The 12 visible-fermion labels of the SM finite spectral triple.
    These are the **distinct** Yukawa-bearing modes; each carries a
    multiplicity (`multOf`) from v0.9 eq. (8405). -/
inductive Fermion
  | top | charm | up
  | bottom | strange | down
  | tau | mu | el
  | nu1 | nu2 | nu3
  deriving DecidableEq, Repr

namespace Fermion

/-- Multiplicity of fermion `f` in the visible spectrum, from
    v0.9 eq. (8405): `2 · color_factor` per Yukawa.

    * Quarks (up, charm, top, down, strange, bottom): color = 3,
      multiplicity = 6.
    * Leptons (tau, mu, el): color = 1, multiplicity = 2.
    * Neutrinos (nu1, nu2, nu3): color = 1, multiplicity = 2. -/
def multOf : Fermion → ℕ
  | top | charm | up | bottom | strange | down => 6
  | tau | mu | el | nu1 | nu2 | nu3 => 2

/-- The sum of all 12 multiplicities equals 48 (= `NVisible`). -/
theorem sum_multOf_eq_48 :
    multOf top + multOf charm + multOf up
    + multOf bottom + multOf strange + multOf down
    + multOf tau + multOf mu + multOf el
    + multOf nu1 + multOf nu2 + multOf nu3 = NVisible := by
  decide

end Fermion

/-! ## Tier-2 named axioms — empirical singular-value inputs

The numerical singular values entering the `κ₂` computation are:

* `M_R / Λ_c`, the dimensionless Majorana scale (v0.9 line 9745
  central reading: `M_R ≈ 0.011 · Λ_c`, with the acceptance window
  `M_R ∈ [3·10¹⁴, 1.5·10¹⁵]` GeV).
* `y_f = √2 m_f / v` for each visible fermion (PDG 2024 running
  masses at `M_Z`).
* `Λ_c = v · e³²` (v0.9 line 9743's definition of the cutoff scale).

These axioms are isolated to this file and never used to derive
themselves.  They are the *only* empirical inputs in the κ₂
computation. -/

/-- **Named axiom — Tier 2.** The dimensionless Majorana mass
    `M_R / Λ_c`. v0.9 line 9745 quotes the central reading
    `M_R / Λ_c = 0.011` (with `M_R ≈ 7 · 10¹⁴` GeV and
    `Λ_c = v e³² ≈ 1.94 · 10¹⁶` GeV).

    **Citation**: Ben-Shalom v0.9 §38 (`rem:f4-failure` line 9745);
    SO(10)-instanton see-saw window `M_R ∈ [3·10¹⁴, 1.5·10¹⁵]` GeV
    (v0.9 `thm:MR-window`). -/
axiom MR_over_Lambda_c : ℝ

/-- Acceptance window: `M_R / Λ_c` lies in the SO(10) instanton see-saw
    window `[3·10¹⁴, 1.5·10¹⁵] GeV / Λ_c ∈ [0.0154, 0.0772]`. -/
axiom MR_over_Lambda_c_in_window :
    (154 / 10000 : ℝ) ≤ MR_over_Lambda_c ∧ MR_over_Lambda_c ≤ 772 / 10000

/-- The natural-log singular-value depth of any hidden mode:
    `ξ_hid := -log(M_R / Λ_c)`. -/
noncomputable def xi_hidden : ℝ := -Real.log MR_over_Lambda_c

/-- **Named axiom — Tier 2.**  The visible-fermion log-singular-value
    depths `ξ_f := -log(m_f / Λ_c)` for each `f ∈ Fermion`.

    These are the multiplicity-1 entries of the singular-value
    spectrum after dividing through by `Λ_c`.

    **Citation**: PDG 2024 (running quark masses, charged-lepton pole
    masses, light-neutrino mass-squared splittings); v0.9 line 9743
    (definition of `Λ_c = v · e³²`). -/
axiom xi_visible : Fermion → ℝ

/-- The visible depths sit in a finite window
    `[ξ_min, ξ_max]` with `ξ_min ≈ 0.006` (top) and `ξ_max ≈ 65.2`
    (lightest neutrino).  Wide bounds suitable for downstream
    rational arithmetic. -/
axiom xi_visible_window :
    ∀ f : Fermion, (0 : ℝ) ≤ xi_visible f ∧ xi_visible f ≤ 70

/-- The 192-mode mass matrix has all singular values **positive**: the
    hidden modes sit at `M_R > 0`, and `m_f > 0` for every Yukawa. -/
theorem MR_over_Lambda_c_pos : 0 < MR_over_Lambda_c := by
  have h := MR_over_Lambda_c_in_window
  linarith [h.1]

theorem MR_over_Lambda_c_lt_one : MR_over_Lambda_c < 1 := by
  have h := MR_over_Lambda_c_in_window
  linarith [h.2]

/-- Hidden-mode depth is positive: `ξ_hid = -log(M_R/Λ_c) > 0` since
    `M_R/Λ_c ∈ (0,1)`. -/
theorem xi_hidden_pos : 0 < xi_hidden := by
  unfold xi_hidden
  have h₁ := MR_over_Lambda_c_pos
  have h₂ := MR_over_Lambda_c_lt_one
  have h₃ : Real.log MR_over_Lambda_c < 0 := Real.log_neg h₁ h₂
  linarith

/-! ## The full singular-value spectrum, structured -/

/-- A bundle carrying the full singular-value-spectrum data:
    the hidden depth, the visible-depth function, and the
    multiplicity assignment. -/
structure FullDFSpectrum where
  /-- Hidden log-depth (all 144 hidden singular values share this). -/
  xiHidden : ℝ
  /-- Visible log-depth function on the 12 distinct Yukawa labels. -/
  xiVisible : Fermion → ℝ
  /-- Each visible depth lies in a finite window. -/
  xiVisible_window : ∀ f, (0 : ℝ) ≤ xiVisible f ∧ xiVisible f ≤ 70
  /-- The hidden depth is positive. -/
  xiHidden_pos : 0 < xiHidden

/-- The canonical SM spectrum, built from the named axioms above.
    Captures the full structural content of v0.9 line 8411. -/
noncomputable def canonical : FullDFSpectrum where
  xiHidden := xi_hidden
  xiVisible := xi_visible
  xiVisible_window := xi_visible_window
  xiHidden_pos := xi_hidden_pos

end SpectralPhysics.Kappa2FromSpectrum
