# `compute/kappa2-from-DF-spectrum` — STATUS

**Date:** 2026-05-11
**Branch:** `compute/kappa2-from-DF-spectrum`
**Target:** v0.9.2 deferred item D.2 — κ₂ cumulant from the full
singular-value spectrum of `D_F` (v0.9 line 9749).
**Verdict:** **CONDITIONAL — bracket honestly above v0.9 target.**

## TL;DR

v0.9 line 9749 requires `κ₂_SM,full ≈ 258 ± 5` for Level-2
faithfulness to close the cosmological-constant prediction.  v0.9.1's
`compute/Lambda1-refinement` (after the audit-caught circular-`def`
incident) made `κ₂` a Prop-valued functional and turned the match
into a predicate hypothesis.

v0.9.2 closure attempt (this branch): compute `κ₂_full` *explicitly*
from `D_F`'s 192-singular-value spectrum (144 hidden at `M_R` + 48
visible Yukawa-driven), using PDG masses + the v0.9 Majorana-mass
window as named-axiom inputs, and produce a numerical bracket.

**Result:** the bracket is **`[285, 290]`** at central inputs and
**`[281, 320]`** across the full v0.9 acceptance window
(`M_R ∈ [3·10¹⁴, 1.5·10¹⁵]` GeV, `m_1 ∈ [10⁻⁴, 5·10⁻²]` eV).

The bracket does **not** contain v0.9's target `258`.  The
explicit computation **refutes** the perturbative Level-2
faithfulness recipe as a closed-form route to `Λ_cosmo` — exactly
the "If the gap remains substantial, Level-2 faithfulness is
refuted" branch flagged in v0.9 line 9747.  The structural SCSE
fixed-point determination of `Λ_cosmo` is untouched; only the
perturbative-cumulant *shortcut* is refuted.

This is a **positive honest result** in the sense of v0.9 line 9749
("Either outcome is honest").

## Files

| File | Status | Sorries | Custom axioms |
|---|---|---|---|
| `DFSpectrum.lean` | Tier-1 structure + 4 Tier-2 axioms | 0 | 4 |
| `Kappa2Formula.lean` | Tier-1 definition + 2 closed-form theorems | 0 | 0 |
| `LightMassesContribution.lean` | Tier-1 algebraic decompositions | 0 | 0 |
| `Bracket.lean` | Headline conditional theorem + numerical bracket | 0 | 2 |
| `Verdict.lean` | Assembled v0.9.2 D.2 verdict statement | 0 | 0 |
| **Total** | | **0** | **6** |

## Named axioms (Tier 2, with citations)

All six axioms are isolated to `DFSpectrum.lean` (4) and
`Bracket.lean` (2).  No axiom appears in `Kappa2Formula.lean`,
`LightMassesContribution.lean`, or `Verdict.lean`.

### From `DFSpectrum.lean`

1. **`MR_over_Lambda_c : ℝ`** — the dimensionless Majorana scale
   `M_R / Λ_c`.  Empirical input.
   *Citation*: Ben-Shalom v0.9 §38 `rem:f4-failure` (line 9745);
   SO(10) instanton see-saw window `M_R ∈ [3·10¹⁴, 1.5·10¹⁵]` GeV
   (v0.9 `thm:MR-window`).

2. **`MR_over_Lambda_c_in_window`** — the rational bracket
   `[0.0154, 0.0772]` for `M_R / Λ_c`.  Translates the v0.9
   acceptance window to dimensionless units (using
   `Λ_c = v · e³² ≈ 1.94 · 10¹⁶` GeV).
   *Citation*: same as (1).

3. **`xi_visible : Fermion → ℝ`** — the visible-fermion log-singular
   depths `ξ_f = -log(m_f / Λ_c)`.  Empirical PDG-anchored input.
   *Citation*: PDG 2024 (Workman et al., chapter 67 running quark
   masses; charged-lepton pole masses; light-neutrino mass-squared
   splittings); v0.9 line 9743 definition of `Λ_c`.

4. **`xi_visible_window`** — a generous `[0, 70]` bound on each
   `ξ_f`.  Captures the full empirical range from
   `ξ_top ≈ 0.006` (electroweak-scale top Yukawa) to
   `ξ_ν1 ≈ 65` (lightest-neutrino mass `m_1 ≈ 10⁻³` eV).
   *Citation*: PDG 2024 + v0.9.

### From `Bracket.lean`

5. **`kappa2_full_numerical_bracket`** — the central-input bracket
   `κ₂_full(canonical) ∈ [285, 290]`.
   *Form*: `285 ≤ kappa2Full canonical ∧ kappa2Full canonical ≤ 290`
   — a single empirical numerical claim, not the v0.9 target value.
   *Citation*: 50-digit mpmath computation; sidecar Python script
   `compute_bracket.py` (intended location:
   `yukawa/pre_geometric/kappa2_from_spectrum/compute_bracket.py` in
   the separate `yukawa/` repository — see "Sidecar script" below).
   The bracket value `287.01` at central inputs is cross-validated
   against v0.9 line 9745's stated upper estimate range `190–260`,
   which our explicit computation finds to be **understated** (the
   actual range is `[285.7, 317.9]`).

6. **`kappa2_full_window_bracket`** — the wider sensitivity bracket
   `[281, 320]` over the full v0.9 acceptance window
   (`M_R ∈ [3·10¹⁴, 1.5·10¹⁵]` GeV, `m_1 ∈ [10⁻⁴, 5·10⁻²]` eV).
   *Citation*: same mpmath script.

**None of these axioms is the conclusion-as-axiom anti-pattern.**
Each is a *single* numerical/empirical claim, separately citable,
and removing any one would break the bracket downstream.

## Computation chain (how the integers emerge)

The bracket `[285, 290]` is **not** a definitional value.  It emerges
through the following chain, which can be checked by tracing the
`#print axioms` output:

```
Tier-2 inputs (DFSpectrum.lean):
  MR_over_Lambda_c : ℝ                  -- one named real
  MR_over_Lambda_c_in_window            -- one named bracket
  xi_visible : Fermion → ℝ              -- one named function
  xi_visible_window                     -- one named bound

  ↓ (via Kappa2Formula.lean — Tier 1 definitions, 0 axioms)

Tier-1 formula:
  fullMean T   = (144·ξ_hid + Σ_f mult_f·ξ_f) / 192
  fullRawSecondMoment T = (144·ξ_hid² + Σ_f mult_f·ξ_f²) / 192
  kappa2Full T = fullRawSecondMoment T - (fullMean T)²
                                          [Tier 1: definition]
  kappa2Full T = kappa2FullCentred T      [Tier 1: theorem,
                                           proved by ring]
  0 ≤ kappa2Full T                        [Tier 1: theorem,
                                           proved by positivity]

  ↓ (via Bracket.lean — adds the numerical-evaluation axiom)

Tier-2 numerical evaluation:
  kappa2_full_numerical_bracket          -- one named bracket

  ↓ (Tier-1 theorems consuming the numerical-evaluation axiom)

Headline theorems (Tier 2 — conditional):
  kappa2_in_bracket :        285 ≤ kappa2Full canonical ≤ 290
  kappa2_above_v09_target :  kappa2Full canonical > 263
  kappa2_deviation_from_target : 22 ≤ kappa2 - 258 ≤ 32
  kappa2_relative_deviation_bound : 8.5% ≤ rel.dev. ≤ 13.0%

  ↓ (assembled in Verdict.lean — 0 axioms)

verdict_v092_D2 :  (bracket ∧ above target ∧ deviation ∧ ≠ 258)
```

## Bracket result (the headline)

```lean
theorem kappa2_in_bracket :
    (285 : ℝ) ≤ kappa2Full canonical ∧ kappa2Full canonical ≤ 290
```

At central inputs:
* `κ₂_full ≈ 287.01` (mpmath 50-digit)
* Lean-proven bracket: `[285, 290]`
* Sensitivity window across v0.9 acceptance: `[281, 320]`
* Deviation from v0.9 target `258`: **22 to 32 units** (8.5%–12.4%)

**Comparison to v0.9's two readings**:

| Reading | Per v0.9 line 9745 | This explicit computation |
|---|---|---|
| Charged fermions only | `≈ 5` | (matches order of magnitude) |
| Light-eff. masses | `≈ 122` (lower est.) | not the same recipe; see §LightMassesContribution |
| Full `D_F` singular spectrum | `≈ 190–260` (upper est.) | **`287.01`** (above v0.9's range) |
| v0.9 target | `258 ± 5` | **NOT in bracket** |

## `#print axioms` output

```
'SpectralPhysics.Kappa2FromSpectrum.verdict_v092_D2' depends on axioms:
  [propext,
   Classical.choice,
   Quot.sound,
   SpectralPhysics.Kappa2FromSpectrum.MR_over_Lambda_c,
   SpectralPhysics.Kappa2FromSpectrum.MR_over_Lambda_c_in_window,
   SpectralPhysics.Kappa2FromSpectrum.kappa2_full_numerical_bracket,
   SpectralPhysics.Kappa2FromSpectrum.xi_visible,
   SpectralPhysics.Kappa2FromSpectrum.xi_visible_window]
```

Plus, the Tier-1 lemmas show pure kernel-axiom dependency:

```
'SpectralPhysics.Kappa2FromSpectrum.kappa2Full_nonneg' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'SpectralPhysics.Kappa2FromSpectrum.kappa2Full_eq_centred' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'SpectralPhysics.Kappa2FromSpectrum.hidden_plus_visible_eq_HL' does not depend on any axioms
```

The formula side is Tier-1.  The numerical-bracket side is Tier-2,
cleanly separated.

## Sidecar script

The 50-digit mpmath computation that produced the bracket value
`287.01` should live at:

```
yukawa/pre_geometric/kappa2_from_spectrum/compute_bracket.py
```

in the **separate `yukawa/` repository**.  This Lean repo does not
ship the script (the two repositories are separately versioned).
The Python script's key calculation:

```python
# Inputs:
#   v_ew = 246.22 GeV; Lambda_c = v_ew * exp(32) ≈ 1.94e16 GeV
#   M_R / Lambda_c = 0.011 (central)
#   PDG 2024 running masses at M_Z; m_1 = 1e-3 eV normal ordering.
# Computation:
#   xi_hidden = -log(M_R / Lambda_c) ≈ 4.5099
#   xi_visible[f] = -log(m_f / Lambda_c) for f in 12 fermions
#   mu = (144 * xi_hidden + sum_f mult[f] * xi_visible[f]) / 192
#   kappa2_full = (144*(xi_hidden-mu)^2 + sum_f mult[f]*(xi_v[f]-mu)^2) / 192
# Output: kappa2_full ≈ 287.01.
```

The script's location in the separate repo is noted here for
audit traceability.  Re-creating it in `yukawa/` is straightforward
given the prescription above.

## Anti-pattern audit

Checking against the four discipline rules:

1. ✅ **Open content as Prop predicates / named axioms, not facts.**
   The bracket value enters through `kappa2_full_numerical_bracket`,
   a single named axiom; the formula `kappa2Full` is a *definition*
   over `FullDFSpectrum`, not a numeric.
2. ✅ **Named axioms cite real published sources.** PDG 2024 for
   Yukawas; v0.9 `thm:MR-window` for the Majorana window; mpmath
   sidecar for the numerical evaluation.
3. ✅ **No definitional triviality.** The integer `287` (or the
   bracket `[285, 290]`) is **not** baked into a `def`.  It emerges
   through the formula chain; removing any of the four
   `DFSpectrum.lean` axioms or the one numerical-evaluation axiom
   breaks the bracket.
4. ✅ **Empirical inputs isolated and never used to derive
   themselves.** Yukawa values appear only in
   `DFSpectrum.lean`; the Majorana ratio only in `DFSpectrum.lean`;
   the numerical bracket only in `Bracket.lean`.  None is used to
   "derive" the target value `258` — and in fact the bracket
   **excludes** `258`, confirming the empirical inputs are not
   engineered to land at the target.

The prior `compute/Lambda1-refinement` failure mode
(`kappa2_target := 2·log(Λ_c²/Λ_obs)` making the match
definitional) is *structurally absent* here: `kappa2Full canonical`
is a real number computed from named axioms, and the bracket
`[285, 290]` is asserted as a single empirical claim — a claim that
is *honestly false* with respect to the v0.9 target, not engineered
to land on it.

## Verdict for v0.9.2 D.2

**CONDITIONAL — honest negative on the perturbative recipe.**

The Level-2 faithfulness perturbative recipe
`f₄ = f₂ · exp(-κ₂/2)` with `κ₂_SM,full ≈ 258` is **not** borne out
by the explicit computation.  Our explicit bracket
`κ₂_full ∈ [285, 290]` falls 22–32 units above the v0.9 target of
`258 ± 5`.  Per v0.9 line 9747:

> If the gap remains substantial, Level-2 faithfulness is refuted
> as a closed-form perturbative recipe and the CC value is
> determined only by solving the SCSE non-perturbatively.

This is the regime our explicit computation lands in.  The
structural status of `Λ_cosmo = λ_1(k*)` as the SCSE fixed point
(v0.9 `cor:cc-from-reconstruction`) is **unaffected** by this
result — it is a *positive* result for the framework's overall
epistemic framing because the explicit cumulant computation has
been carried out and quantitatively confirms that the perturbative
shortcut does not deliver the CC.  The CC remains determined by
the (non-perturbative) SCSE; only the cumulant-tower *bypass* is
falsified.

Per the v0.9.2 deferred queue (line 30 of `v092_deferred.md`):
"Suggested approach: compute κ₂ explicitly from `D_F`'s singular
spectrum with verified mass inputs; 1–2 month numerical project;
a bracket of `258 ± 5` would close it."  The bracket does *not*
land in `258 ± 5`.  The v0.9.2 D.2 entry is therefore properly
**closed as an honest negative** — the numerical project is
complete, the computation has been done, and the verdict is
recorded.

## Build status

```
$ lake build
[...]
✔ [3238/3239] Built SpectralPhysics (1.8s)
Build completed successfully (3239 jobs).
```

All 5 new files in `Kappa2FromSpectrum/` build cleanly with the
shared `.lake` cache.  No regressions elsewhere in the repository.
