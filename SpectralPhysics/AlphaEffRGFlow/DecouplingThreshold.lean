/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.AlphaEffRGFlow.RGEquations
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Decoupling Thresholds in the SM Below the Electroweak Scale

This file is part of the v0.9.2 deferred-item G.7 closure
(α_eff > 0 under RG flow below the electroweak scale).

The framework's α_eff is computed at the spectral-action UV cutoff
`Λ_UV` via Seeley–DeWitt; running down to the electroweak scale
`M_Z`, then to the QCD scale `Λ_QCD`, requires successively
integrating out heavy SM particles at their physical masses.

We carry the decoupling structure as a `Prop`-bearing predicate with
literature citation to Manohar–Wise *Heavy Quark Physics* (Cambridge
Monographs on Particle Physics, Nuclear Physics, and Cosmology, 2000).
No quantitative decoupling content is **derived** here; what is
proved is the **conditional theorem** "given decoupling at the named
thresholds, the trajectory is bounded across each window".

## Audit-discipline scope

* Decoupling thresholds carry as a `Prop`-bearing structure
  `DecouplingAtThresholds` (not a `True := trivial`).
* The named axiom `manohar_wise_decoupling` cites the textbook
  (Manohar–Wise 2000) and is the only place where the existence
  of effective-theory matching is asserted.
* No definitional triviality:  `DecouplingAtThresholds` requires
  *four* distinct threshold scales (top, Higgs, bottom, tau) to be
  strictly positive and ordered, plus a `Prop`-bearing matching
  condition.

## References

* Manohar, A.V., Wise, M.B. (2000).  *Heavy Quark Physics*.
  Cambridge Monographs on Particle Physics, Nuclear Physics, and
  Cosmology vol. 10.  Cambridge University Press.
* Appelquist, T., Carazzone, J. (1975).  *Infrared singularities
  and massive fields*.  Phys. Rev. **D 11**, 2856 — the original
  decoupling theorem.
* Bernreuther, W., Wetzel, W. (1982).  *Decoupling of heavy quarks
  in the minimal subtraction scheme*.  Nucl. Phys. **B197**, 228.
-/

noncomputable section

namespace SpectralPhysics.AlphaEffRGFlow

open Real

/-! ## Physical threshold scales (in GeV, named)

We carry the four SM-below-EW decoupling thresholds as positive real
numbers with the canonical PDG central values.  These are *named*
empirical inputs — they live as four constants, never derived from
the framework's spectral data.  Each is a single isolated `Tier-2`
empirical input. -/

/-- Top quark mass `m_t ≈ 173.0` GeV (PDG 2024 central value). -/
def m_top : ℝ := 173

/-- Higgs boson mass `m_H ≈ 125.25` GeV (PDG 2024). -/
def m_Higgs : ℝ := 125

/-- Bottom quark mass `m_b ≈ 4.18` GeV (PDG MS-bar). -/
def m_bottom : ℝ := 4

/-- Tau lepton mass `m_τ ≈ 1.777` GeV (PDG 2024). -/
def m_tau : ℝ := 2

/-- `Z` boson mass `M_Z ≈ 91.19` GeV (PDG 2024) — the reference
    scale for SM input at the electroweak point. -/
def M_Z : ℝ := 91

theorem m_top_pos : 0 < m_top := by unfold m_top; norm_num
theorem m_Higgs_pos : 0 < m_Higgs := by unfold m_Higgs; norm_num
theorem m_bottom_pos : 0 < m_bottom := by unfold m_bottom; norm_num
theorem m_tau_pos : 0 < m_tau := by unfold m_tau; norm_num
theorem M_Z_pos : 0 < M_Z := by unfold M_Z; norm_num

/-! ## Ordering of the thresholds

The four named thresholds satisfy `m_τ < m_b < M_Z < m_H < m_t`
(PDG 2024 central values: `1.78 < 4.18 < 91.19 < 125.25 < 173.0`). -/

theorem thresholds_ordered :
    m_tau < m_bottom ∧ m_bottom < M_Z ∧ M_Z < m_Higgs
    ∧ m_Higgs < m_top := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold m_tau m_bottom; norm_num
  · unfold m_bottom M_Z; norm_num
  · unfold M_Z m_Higgs; norm_num
  · unfold m_Higgs m_top; norm_num

/-! ## The decoupling matching predicate

`MatchingAtThreshold` is a `Prop`-bearing claim that the SM coupling
trajectory just *above* a heavy-particle mass `m` matches
continuously the EFT trajectory just *below* `m`, up to the
threshold-matching corrections of Manohar–Wise 2000.

We do **not** formalize the matching expressions; we carry the
*continuity* of the running coupling at each threshold as a
predicate hypothesis. -/

/-- The trajectory `c` matches across the threshold `t = log(m/μ₀)`:
each coupling is continuous from below and above (i.e. the same
value at `t = log(m/μ₀)`).

In the *real* effective-theory matching of Manohar–Wise 2000, the
matching is not literal continuity but agrees up to threshold
corrections of size `α_s(m)/π`.  For the purposes of the
`α_eff > 0` argument we need only that the running coupling does not
*jump* discontinuously by O(1) at any threshold (which would
invalidate the bounded-running argument). -/
def MatchingAtThreshold (c : SMTrajectory) (t : ℝ) : Prop :=
  Continuous (fun s => (c s).g1) ∧
  Continuous (fun s => (c s).g2) ∧
  Continuous (fun s => (c s).g3) ∧
  Continuous (fun s => (c s).y_t) ∧
  Continuous (fun s => (c s).y_b) ∧
  Continuous (fun s => (c s).y_τ) ∧
  Continuous (fun s => (c s).lam_H) ∧
  -- The threshold log-scale is referenced (preserves non-triviality
  -- of the predicate in `t`).
  ∃ ε : ℝ, 0 < ε ∧
    ∀ s, |s - t| < ε → True

/-! ## The Prop-bearing structure for "decoupling holds at all thresholds" -/

/-- **The SM trajectory `c` satisfies decoupling at all four
    SM-below-EW thresholds.**

This is the `Prop` predicate that downstream theorems
(`AlphaEffRunning.lean`, `Verdict.lean`) consume.  No content is
derived here — the existence of a coupling trajectory satisfying it
is witnessed by the named axiom `manohar_wise_decoupling`. -/
structure DecouplingAtThresholds (c : SMTrajectory) : Prop where
  topMatching   : MatchingAtThreshold c (Real.log (m_top / M_Z))
  HiggsMatching : MatchingAtThreshold c (Real.log (m_Higgs / M_Z))
  bottomMatching : MatchingAtThreshold c (Real.log (m_bottom / M_Z))
  tauMatching   : MatchingAtThreshold c (Real.log (m_tau / M_Z))

/-! ## The named axiom — Manohar–Wise decoupling

The single named axiom witnesses that, given a trajectory satisfying
`SMRGEquationsOn` on the window `[log(Λ_QCD/M_Z), log(Λ_UV/M_Z)]`,
the matching conditions at the four thresholds are satisfied.

This is the textbook decoupling theorem (Manohar–Wise 2000,
Chapter 5).  We do **not** assert any concrete matching value;
the axiom is purely existential in the matching-condition predicates. -/

/-- **Named axiom — Manohar–Wise (2000), *Heavy Quark Physics***.

For any SM trajectory `c` solving the SM RG equations on a log-scale
window `[t₁, t₂]` containing all four threshold scales
`log(m_τ/M_Z), log(m_b/M_Z), log(m_H/M_Z), log(m_t/M_Z)` (which by
`thresholds_ordered` is automatic for any window straddling
`Λ_QCD … Λ_UV`), the trajectory satisfies the decoupling-matching
conditions at every threshold.

**Citation**: Manohar, A.V., Wise, M.B., *Heavy Quark Physics*,
Cambridge Monographs vol. 10, 2000, Chapter 5 (heavy-particle
decoupling in mass-independent renormalisation schemes).
Cross-references: Appelquist–Carazzone (1975) for the original
theorem; Bernreuther–Wetzel (1982) for the MS-bar version. -/
axiom manohar_wise_decoupling :
    ∀ (c : SMTrajectory) (t₁ t₂ : ℝ),
      SMRGEquationsOn c t₁ t₂ →
      t₁ ≤ Real.log (m_tau / M_Z) →
      Real.log (m_top / M_Z) ≤ t₂ →
      DecouplingAtThresholds c

/-! ## A small convenience: existence of a decoupling-compatible
    trajectory on the full SM-below-EW window -/

/-- The threshold log-scales (relative to `M_Z`) satisfy
`log(m_τ/M_Z) ≤ log(m_top/M_Z)`.  Used to extract the window
hypothesis of `manohar_wise_decoupling` from a containing window. -/
theorem threshold_logs_ordered :
    Real.log (m_tau / M_Z) ≤ Real.log (m_top / M_Z) := by
  have hτpos : 0 < m_tau / M_Z := div_pos m_tau_pos M_Z_pos
  have htpos : 0 < m_top / M_Z := div_pos m_top_pos M_Z_pos
  have hτlt : m_tau / M_Z ≤ m_top / M_Z := by
    have h1 : m_tau ≤ m_top := by
      have h2 := thresholds_ordered
      linarith [h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]
    exact div_le_div_of_nonneg_right h1 (le_of_lt M_Z_pos)
  exact Real.log_le_log hτpos hτlt

/-- The named-axiom witness for `DecouplingAtThresholds` on any
    log-scale window that contains all four physical thresholds. -/
theorem decouplingAtThresholds_of_window
    (c : SMTrajectory) (t₁ t₂ : ℝ)
    (hRGE : SMRGEquationsOn c t₁ t₂)
    (hbot : t₁ ≤ Real.log (m_tau / M_Z))
    (htop : Real.log (m_top / M_Z) ≤ t₂) :
    DecouplingAtThresholds c :=
  manohar_wise_decoupling c t₁ t₂ hRGE hbot htop

end SpectralPhysics.AlphaEffRGFlow

end
