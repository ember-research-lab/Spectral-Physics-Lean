/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Visible-sector Yukawa couplings and their multiplicities

This file fixes the data feeding into the Self-Model Deficit theorem
(`thm:self-model-deficit`, v0.9 lines 8435–8444):

  `−ζ̃'_vis(0) = dim(H_hid) = 288`,

equivalently (line 8441–8443)

  `Π_{f ∈ vis} y_f^{mult_f} = e^{-288}`.

The data of the identity decomposes into

* **multiplicities** `mult_f`, fixed by the finite Dirac operator
  decomposition of `H_F` from Proposition `prop:zeta-explicit`
  (v0.9 eq. (8405)):
  ```
  ζ̃(s) = 144 M_s^{-s}
       + 2 [ 3·Σ_up y_f^{-s}  +  3·Σ_down y_f^{-s}
            +  Σ_lep y_f^{-s}  +  Σ_ν y_f^{-s} ];
  ```
  hence `mult_q = 6` (color factor 3 × particle/anti factor 2),
  `mult_ℓ = 2` (no color × particle/anti factor 2),
  `mult_ν = 2`.

* **Yukawa couplings** `y_f`, fixed by *measurement* (PDG masses at
  electroweak scale `v = 246.22 GeV`, with the convention
  `y_f = √2 · m_f / v`).
  These are inputs from observation, not derivations of the framework;
  they enter the Lean development as named **`axiom`** declarations
  with explicit citations.

* **Per-sector log-Yukawa sums** `S_up`, `S_down`, `S_lep`, `S_ν`,
  which are the manuscript's *quoted* values of
  `Σ mult_f · (−log y_f)` per sector
  (v0.9 lines 8474–8482, the "Numerical verification" table).
  These are likewise **`axiom`**-level inputs: they are the numerical
  values reported by the manuscript, computed from the PDG Yukawas at
  the specific RG-running scheme employed by v0.9.

  This file does **not** re-derive the table. It encodes the four
  numbers and proves the four arithmetic facts that close out the
  charged subtotal `277.39`, light-ν `184.62`, and so on.

## Tier classification

* **Tier 1 (proved here)**: the multiplicity definitions, the
  multiplicity totals (`6+6+6 = 18` up modes, etc.), and the algebraic
  identities relating per-sector totals to the published table.

* **Tier 2 (named axioms, with PDG citations)**: the numerical Yukawa
  values themselves and the manuscript's per-sector log-Yukawa totals.
  Replacing these axioms with closed-form derivations is open in v0.9
  (line 8463–8465 explicitly says so).

## References

* Ben-Shalom, "Spectral Physics", v0.9, Chapter 24:
  - Proposition `prop:zeta-explicit` (line 8402, eq. 8405).
  - Proposition `thm:self-model-deficit` (line 8435).
  - Numerical table (lines 8474–8482).
* Particle Data Group, *Review of Particle Physics*, 2024
  (Workman et al.). Charged-fermion masses at electroweak scale.
* `pre_geometric/B2_yukawa_map/yukawa_assignment.py` — the
  framework's own Python implementation of the same identity, used
  here to cross-validate the table.
-/

namespace SpectralPhysics.SelfModelDeficit

open Real

/-! ## Multiplicities — Tier 1 -/

/-- Multiplicity of a single up-type quark Yukawa (`y_t`, `y_c`, `y_u`)
    in the finite spectral triple.  From v0.9 eq. (8405), the prefactor
    is `2 · 3 = 6`: color factor 3, particle/anti factor 2. -/
def multUp : ℕ := 6

/-- Multiplicity of a single down-type quark Yukawa (`y_b`, `y_s`, `y_d`).
    Same structural origin as `multUp`. -/
def multDown : ℕ := 6

/-- Multiplicity of a single charged-lepton Yukawa (`y_τ`, `y_μ`, `y_e`).
    From v0.9 eq. (8405): no color factor, particle/anti factor 2. -/
def multLep : ℕ := 2

/-- Multiplicity of a single Dirac-light-neutrino Yukawa
    (`y_{ν_1}`, `y_{ν_2}`, `y_{ν_3}`).  Same structural origin as
    `multLep`: no color factor, particle/anti factor 2. -/
def multNu : ℕ := 2

/-! ## Mode counts (the "Modes" column of v0.9 table) -/

/-- 18 up-quark modes (3 generations × `multUp = 6`). -/
theorem up_modes_eq_18 : 3 * multUp = 18 := by
  unfold multUp; decide

/-- 18 down-quark modes. -/
theorem down_modes_eq_18 : 3 * multDown = 18 := by
  unfold multDown; decide

/-- 6 charged-lepton modes (3 × 2). -/
theorem lep_modes_eq_6 : 3 * multLep = 6 := by
  unfold multLep; decide

/-- 6 light-neutrino modes (3 × 2). -/
theorem nu_modes_eq_6 : 3 * multNu = 6 := by
  unfold multNu; decide

/-- The four sectors carry `18 + 18 + 6 + 6 = 48` visible modes,
    matching the visible-eigenvalue count from
    `prop:zeta-explicit`. -/
theorem total_visible_modes :
    3 * multUp + 3 * multDown + 3 * multLep + 3 * multNu = 48 := by
  unfold multUp multDown multLep multNu; decide

/-! ## Visible Yukawa couplings — named axioms (PDG values) -/

/-- The visible-sector Yukawa coupling for a fermion `f`.
    Values are fixed empirically (PDG 2024 charged-fermion masses
    at the electroweak scale `v = 246.22 GeV`, with the convention
    `y_f = √2 · m_f / v`).  Neutrino Yukawas use the *Dirac* coupling
    in the type-I see-saw with `m_1 ≈ 0.001 eV` (normal ordering). -/
inductive VisFermion
  | top | charm | up
  | bottom | strange | down
  | tauL | muL | eL
  | nu1 | nu2 | nu3
  deriving DecidableEq, Repr

namespace VisFermion

/-- Yukawa coupling `y_f` of fermion `f`, fixed empirically.

    See `Yukawas.lean` docstring for the convention.  This is the
    framework's *empirical input*, not a derivation. -/
axiom y : VisFermion → ℝ

/-- Each Yukawa is positive (PDG masses are positive). -/
axiom y_pos : ∀ f : VisFermion, 0 < y f

/-- Each Yukawa is strictly less than 1 (the top is the largest, and
    `y_t = √2 m_t/v ≈ 0.994 < 1` at `M_Z`).  This is needed to make
    `−log y_f` non-negative for every visible fermion. -/
axiom y_lt_one : ∀ f : VisFermion, y f < 1

end VisFermion

open VisFermion

/-! ## Per-fermion log contribution -/

/-- The per-fermion contribution `−log y_f`.

    For visible Yukawas `y_f ∈ (0, 1)`, `Real.log y_f ≤ 0` so this is
    `≥ 0` — the spectral information content of a single mode of
    fermion `f`.

    Note: `noncomputable` since `Real.log` is. -/
noncomputable def negLogY (f : VisFermion) : ℝ := -Real.log (y f)

/-- `−log y_f ≥ 0` for every visible fermion. -/
theorem negLogY_nonneg (f : VisFermion) : 0 ≤ negLogY f := by
  unfold negLogY
  have h1 : 0 < y f := y_pos f
  have h2 : y f < 1 := y_lt_one f
  have h3 : Real.log (y f) < 0 := Real.log_neg h1 h2
  linarith

/-! ## Per-sector log-Yukawa totals — Tier 2 named axioms

The four numbers below are the v0.9 manuscript's quoted per-sector
log-Yukawa sums from the table on lines 8474–8482, *with multiplicities
already absorbed*.  They are inputs from PDG measurements run to the
v0.9 RG scheme; the framework does not derive them.

The next file (`SeeSawCancel.lean`) imposes the constraint that they
sum to 288 with the see-saw correction.  The headline theorem
(`ZetaPrimeZero.lean`) chains them together. -/

/-- The up-quark sector contribution
    `S_up = 6·(−log y_t − log y_c − log y_u) = 97.23`
    (v0.9 line 8474). -/
noncomputable def S_up : ℝ := 9723 / 100

/-- The down-quark sector contribution
    `S_down = 6·(−log y_b − log y_s − log y_d) = 130.70`
    (v0.9 line 8475). -/
noncomputable def S_down : ℝ := 13070 / 100

/-- The charged-lepton sector contribution
    `S_lep = 2·(−log y_τ − log y_μ − log y_e) = 49.46`
    (v0.9 line 8476). -/
noncomputable def S_lep : ℝ := 4946 / 100

/-- The light-neutrino sector contribution
    `S_νL = 2·(−log y_{ν₁} − log y_{ν₂} − log y_{ν₃}) = 184.62`
    (v0.9 line 8479) — assumes `m_1 ≈ 0.001 eV`, normal ordering. -/
noncomputable def S_nuL : ℝ := 18462 / 100

/-- The heavy right-handed neutrino contribution
    `S_νR = -174.01` (v0.9 line 8480) — induced by the see-saw
    cancellation with `M_R ≈ 7 × 10¹⁴ GeV`. -/
noncomputable def S_nuR : ℝ := -17401 / 100

/-- The visible-sector charged subtotal `S_charged = S_up + S_down + S_lep`.
    From v0.9 line 8478: `S_charged = 277.39`. -/
noncomputable def S_charged : ℝ := S_up + S_down + S_lep

/-- The visible-sector charged subtotal evaluates to `277.39`. -/
theorem S_charged_eq : S_charged = 27739 / 100 := by
  unfold S_charged S_up S_down S_lep
  norm_num

/-- The full visible-sector log-Yukawa sum (with see-saw):
    `S_total = S_charged + S_νL + S_νR`. -/
noncomputable def S_total : ℝ := S_charged + S_nuL + S_nuR

/-! ## The framework prediction encoded as `Tier 2` axioms

The numerical claim that the per-sector totals match the v0.9 table is
*itself* an empirical fact (running PDG masses to the v0.9 RG scheme).
We expose it as a single axiom that pins each sector value to the
table's published number.  Concretely: it asserts that the
multiplicity-weighted sum of `−log y_f` for each sector equals the
corresponding `S_*` constant.

The fourth axiom (the see-saw closed form) lives in `SeeSawCancel.lean`.
-/

/-- **Named axiom — Tier 2.**  The up-quark log-Yukawa sum reported
    in v0.9 table line 8474.

    This is the *numerical content* of running the PDG up-type quark
    masses (`m_t = 173.0 GeV`, `m_c = 0.62 GeV`, `m_u ≈ 1.27 MeV`,
    all at `M_Z` in MS-bar) to the v0.9 RG scheme.

    **Citation**: PDG 2024, Workman et al., chapter 67 (running quark
    masses); v0.9 line 8474. -/
axiom up_sector_log_yukawa_sum :
    (multUp : ℝ) * (negLogY .top + negLogY .charm + negLogY .up) = S_up

/-- **Named axiom — Tier 2.**  Down-quark log-Yukawa sum (v0.9 line 8475).
    PDG masses `m_b ≈ 2.86`, `m_s ≈ 55 MeV`, `m_d ≈ 2.7 MeV` at `M_Z`. -/
axiom down_sector_log_yukawa_sum :
    (multDown : ℝ) * (negLogY .bottom + negLogY .strange + negLogY .down)
      = S_down

/-- **Named axiom — Tier 2.**  Charged-lepton log-Yukawa sum
    (v0.9 line 8476).  PDG pole masses
    `m_τ = 1.7768 GeV`, `m_μ = 105.66 MeV`, `m_e = 0.5110 MeV`. -/
axiom lep_sector_log_yukawa_sum :
    (multLep : ℝ) * (negLogY .tauL + negLogY .muL + negLogY .eL) = S_lep

/-- **Named axiom — Tier 2.**  Light-neutrino Dirac log-Yukawa sum
    (v0.9 line 8479).  Assumes `m_1 ≈ 0.001 eV`, normal ordering, with
    `Δm²_21 = 7.53 × 10⁻⁵ eV²` and `|Δm²_31| = 2.453 × 10⁻³ eV²`. -/
axiom light_nu_sector_log_yukawa_sum :
    (multNu : ℝ) * (negLogY .nu1 + negLogY .nu2 + negLogY .nu3) = S_nuL

/-! ## Sanity arithmetic on the published table -/

/-- The charged subtotal `277.39 = 97.23 + 130.70 + 49.46` (v0.9 line 8478). -/
theorem charged_subtotal_decimal :
    S_up + S_down + S_lep = 27739 / 100 := S_charged_eq

/-- The total *before* see-saw `S_pre := S_charged + S_νL`. -/
noncomputable def S_pre : ℝ := S_charged + S_nuL

/-- `S_pre = 277.39 + 184.62 = 462.01`, the full pre-see-saw sum.

    The framework's claim is that the see-saw contribution
    `S_νR = -174.01` corrects this to exactly `288`. -/
theorem S_pre_eq : S_pre = 46201 / 100 := by
  unfold S_pre S_charged S_up S_down S_lep S_nuL
  norm_num

/-- `S_total = S_pre + S_νR = 462.01 - 174.01 = 288`. -/
theorem S_total_eq_288 : S_total = 288 := by
  unfold S_total S_charged S_up S_down S_lep S_nuL S_nuR
  norm_num

end SpectralPhysics.SelfModelDeficit
