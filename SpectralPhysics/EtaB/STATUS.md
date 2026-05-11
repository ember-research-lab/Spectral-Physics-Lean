# EtaB — Disambiguation between Formula A (`λ^14`) and Formula B (`J²/2`)

**Date:** 2026-05-09
**Branch:** `compute/etaB-disambiguation`
**Build:** `lake build SpectralPhysics.EtaB.Verdict` succeeds (1976 jobs).

## Files

| File                | Status                                     |
| ------------------- | ------------------------------------------ |
| `EtaB/Formulas.lean`   | Tier 1, 0 sorry, **3 named axioms**     |
| `EtaB/Comparison.lean` | Tier 1, 0 sorry, **2 named axioms**     |
| `EtaB/Verdict.lean`    | Tier 1, 0 sorry, **0 axioms**           |

## What got proved (Tier 1, machine-checked)

In `Formulas.lean`:
* `lambdaC_closed_form         : lambdaC = (150 - 23·√5)/440`
* `lambdaC_pos                 : 0 < lambdaC`
* `etaB_FormulaA_pos           : 0 < etaB_FormulaA`
* `etaB_FormulaA_nonneg        : 0 ≤ etaB_FormulaA`
* `etaB_FormulaB_pos           : 0 < etaB_FormulaB`

In `Comparison.lean`:
* `cabibbo_gt_223              : 0.223 < cabibboParam`
* `cabibbo_lt_225              : cabibboParam < 0.225`
* `cabibbo_gt_22397            : 0.22397 < cabibboParam`   *(tighter)*
* `cabibbo_lt_22403            : cabibboParam < 0.22403`   *(tighter)*
* **`etaB_FormulaA_upper       : etaB_FormulaA < 8.1e-10`**
* **`etaB_FormulaA_lower       : 7.9e-10 < etaB_FormulaA`**
* `etaB_FormulaA_gt_observed   : etaB_observed < etaB_FormulaA`
* **`etaB_FormulaB_exact       : etaB_FormulaB = 4.5e-10`**
* `etaB_FormulaB_lt_observed   : etaB_FormulaB < etaB_observed`
* `excessA_pos                 : 0 < excessA`
* `deficitB_pos                : 0 < deficitB`
* `excessA_bracket             : 1.8e-10 < excessA ∧ excessA < 2.0e-10`
* `deficitB_exact              : deficitB = 1.6e-10`
* `abs_dev_A`, `abs_dev_B`     : signed/absolute identification
* **`deficitB_lt_excessA       : deficitB < excessA`**
* **`abs_deviation_compare     :
        |etaB_FormulaB − etaB_observed| < |etaB_FormulaA − etaB_observed|`**

In `Verdict.lean`:
* `framework_endorsed_etaB             := etaB_FormulaB`        *(definition)*
* `framework_endorsed_eq_FormulaB`     : `= etaB_FormulaB`     (`rfl`)
* `framework_endorsed_value`           : `= 4.5e-10`
* `framework_endorsed_beats_FormulaA`  : closer than Formula A
* `framework_endorsed_pos`             : `> 0`
* `framework_endorsed_lt_observed`     : `< etaB_observed`

## What got `sorry`-d

**None.** Zero `sorry` occurrences across all three files.

## What got axiomatized (5 named axioms)

### `Jarlskog : ℝ` (Formulas.lean)

**Category:** `(c) numerical claim awaiting axiomatization` —
specifically observational input.

The Jarlskog CP-violation invariant of the CKM matrix.  *Not*
framework-derived: the spectral-physics framework currently fixes
the CKM phase `δ_CKM = π/φ²` (proved in `CPPhase.lean`) but does
not predict the absolute Cabibbo angle plus the other two CKM
angles to PDG precision in closed form, so `J = c₁₂ c₁₃² s₁₂ s₁₃
s₂₃ sin(δ)` is an external input.

### `Jarlskog_pos : 0 < Jarlskog`

Auxiliary positivity claim, follows from PDG central value.

### `Jarlskog_value : Jarlskog = 3.00e-5`

**Reference:** PDG 2024 review of CP violation in the quark
sector, "Best fit" central value
`J = 3.00^{+0.15}_{-0.09} × 10⁻⁵`.

### `etaB_observed : ℝ` (Comparison.lean)

**Category:** `(c) numerical claim awaiting axiomatization` —
observational input.

The cosmic baryon-to-photon ratio measured by the Planck
satellite.  Not derivable from the framework axioms in Lean
without the full BBN + CMB Boltzmann-equation infrastructure.

### `etaB_observed_value : etaB_observed = 6.10e-10`

**Reference:** Planck Collaboration 2018, *Planck 2018 results.
VI. Cosmological parameters*, A&A 641 (2020) A6, table 2,
extracted from `100 Ω_b h² = 2.237 ± 0.015` via the standard
relation `η_B = 273.36 × Ω_b h² × 10⁻¹⁰ / (T_CMB/2.725 K)³`,
giving `η_B = (6.12 ± 0.04) × 10⁻¹⁰`.  We use the rounded central
value `6.10 × 10⁻¹⁰` for compactness; the precise uncertainty does
not affect the verdict.

## Numerical values (Lean-bracketed)

| Quantity               | Value (Lean)                   | Value (FP)        |
| ---------------------- | ------------------------------ | ----------------- |
| `λ_C`                  | `∈ (0.22397, 0.22403)`         | `≈ 0.224024`      |
| `etaB_FormulaA = λ^14` | `∈ (7.9, 8.1) × 10⁻¹⁰`         | `≈ 8.019 × 10⁻¹⁰` |
| `etaB_FormulaB = J²/2` | `= 4.5 × 10⁻¹⁰` (exact)        | `= 4.5 × 10⁻¹⁰`   |
| `etaB_observed`        | `= 6.10 × 10⁻¹⁰` (named axiom) | Planck 2018       |
| `excessA  = A − obs`   | `∈ (1.8, 2.0) × 10⁻¹⁰`         | `≈ 1.92 × 10⁻¹⁰`  |
| `deficitB = obs − B`   | `= 1.6 × 10⁻¹⁰` (exact)        | `= 1.6 × 10⁻¹⁰`   |

## Comparison results

* **`|dev_B| < |dev_A|`** — proved as `abs_deviation_compare`,
  Tier 1, no extra axiom.  Numerically `1.6 × 10⁻¹⁰ < (1.8 to
  2.0) × 10⁻¹⁰`, so Formula B is at least `0.2 × 10⁻¹⁰` (and at
  most `0.4 × 10⁻¹⁰`) closer to the observed value than Formula A.

* **Sign asymmetry**: Formula A *overshoots* the observed value
  (`etaB_FormulaA > etaB_observed`); Formula B *undershoots*
  (`etaB_FormulaB < etaB_observed`).  Both proved as Tier 1
  theorems.

## The verdict

**The framework's standing prediction is Formula B** —
`η_B = J²/2 = 4.5 × 10⁻¹⁰`.

Reasons (both pointing the same direction):

1. **Numerical** — Lean-proved `|dev_B| < |dev_A|`.
2. **Documentation** — sandbox `sr-resonance-yukawa.tex`
   line 248 explicitly deprecates Formula A in favour of
   Formula B; v0.9's `prop:eta` is the standing inconsistency
   that this branch resolves.

Encoded in Lean as `framework_endorsed_etaB := etaB_FormulaB`
(a *definition*, not a theorem — the framework picks one;
Lean records the choice and the supporting comparisons).

## Honest caveat exposed by Lean

The task spec quoted Formula A as giving `λ^14 ≈ 4.4 × 10⁻¹⁰`,
which would have placed Formula A *below* the observed value
(same side as Formula B), making the disambiguation a
near-tie.

Direct evaluation of `(0.224024)^14` instead gives
`≈ 8.019 × 10⁻¹⁰` — roughly **twice** the figure quoted in the
audit text.  The Lean upper bound `etaB_FormulaA < 8.1 × 10⁻¹⁰`
combined with the lower bound `7.9 × 10⁻¹⁰ < etaB_FormulaA`
makes this rigorous: Formula A *cannot* equal `4.4 × 10⁻¹⁰`.

This is an example of Lean catching an arithmetic error in the
prior text-only audit.  The verdict (Formula B wins) survives,
but the *reason* it wins changes from a marginal numerical
edge to a clear one (Formula A is ~`1.92 × 10⁻¹⁰` from
observed, Formula B is `1.6 × 10⁻¹⁰`).

A separate consequence: any v0.9 narrative built on
"`λ^14 ≈ 4.4 × 10⁻¹⁰` matches `η_B^obs`" should be flagged.
The actual prediction of `prop:eta` is `≈ 8 × 10⁻¹⁰`, which
agrees with observation only at the `~30%` level (and is on
the wrong side of the central value).  The deprecation in
`sr-resonance-yukawa.tex` was therefore well-motivated even
on numerical grounds alone.

## Build status

```
lake build SpectralPhysics.EtaB.Formulas    ← success
lake build SpectralPhysics.EtaB.Comparison  ← success
lake build SpectralPhysics.EtaB.Verdict     ← success
lake build                                   ← success (1976 jobs total)
```

## Commit log on this branch

```
583f645 feat(etaB): state Formula A (λ^14) and Formula B (J²/2) for η_B
aa4af1d feat(etaB): bracket and compare both formulas against Planck 2018
<next>  feat(etaB): record framework verdict + STATUS
```
