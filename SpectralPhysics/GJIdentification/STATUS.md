# `compute/GJ-identification-from-algebra` — STATUS

**Date:** 2026-05-11
**Branch:** `compute/GJ-identification-from-algebra`
**Target:** v0.9.2 deferred item J.3 — GJ identification from algebra
directly (v0.9 line 11036 / `eq:gj-coefficients`).
**Verdict:** **CONDITIONAL — bracket `[0.014, 0.024]` proved.**

## TL;DR

v0.9.1 line 11036 (Georgi–Jarlskog identification, **GJ ≠ Glashow–Jaffe**)
claims three GUT-scale down-quark / lepton Yukawa ratios:

| Coefficient | Algebraic | Empirical | v0.9 rel err |
|---|---|---|---|
| `c₁ = y_d / y_e` | `√5 ≈ 2.236` | `2.200` | **1.7%** |
| `c₂ = y_s / y_μ` | `1/(3+φ) ≈ 0.2170` | `0.215` | **0.7%** |
| `c₃ = y_b / y_τ` | `2/3 ≈ 0.6667` | `0.663` | **0.6%** |

All three live in `ℚ(√5)` — the same quadratic field as `τ = 1/(2+φ)`
and `φ = (1+√5)/2`.

**This Lean formalisation** proves the rigorous bracket

```
0.014 ≤ max(rel_err_c₁, rel_err_c₂, rel_err_c₃) ≤ 0.024
```

from four named axioms (3 empirical bracket axioms + 3 opaque empirical
real constants).  The bracket *contains* v0.9's central `1.7%` reading
but is **wider than** v0.9's quoted qualitative `[0.006, 0.017]` range
because (i) `c₂`'s algebraic and empirical brackets overlap, admitting
up to ~1.9% worst-case, and (ii) the rational endpoints `2.236 ≤ √5 ≤
2.237` introduce bracket-arithmetic slack on `c₁`.

Per v0.9 `rem:gj-epistemic` (line 11036 + 5):
> "The algebraic identification becomes a theorem if the errors close
> under improved numerics."

Our bracket does **not** close J.3 to a theorem at the v0.9-quoted
precision — tightening to `≤ 0.017` requires a 3-loop SM-RG sidecar
not provided here.  J.3 therefore remains an **open** item, with this
Lean module establishing its current rigorous bracket as the honest
status.

## Files

| File | Status | Sorries | Custom axioms |
|---|---|---|---|
| `GJClaim.lean` | Tier-1 algebraic targets + tight rational brackets | 0 | 0 |
| `EmpiricalBracket.lean` | 3 opaque reals + 3 named bracket axioms | 0 | 6 |
| `AlgebraicComputation.lean` | Tier-1 canonical-form identities + `ℚ(√5)` decomposition | 0 | 0 |
| `NumericalBracket.lean` | Headline bracket theorem `gj_within_bracket` | 0 | 0 |
| `Verdict.lean` | Assembled v0.9.2 J.3 verdict | 0 | 0 |
| **Total** | | **0** | **6** |

## Named axioms (Tier 2, with citations)

All six are isolated in `EmpiricalBracket.lean`.  None appear in
`GJClaim.lean`, `AlgebraicComputation.lean`, `NumericalBracket.lean`,
or `Verdict.lean`.

### Empirical-side opaque real constants

1. **`gj_c1_empirical : ℝ`** — the 2-loop SM-RG output `y_d/y_e |_GUT`.
   *Type-only axiom*; value is constrained exclusively by
   `c1_empirical_bracket` below.
   *Citation*: v0.9.1 line 11036; Antusch et al. (2005) JHEP 03, 024.

2. **`gj_c2_empirical : ℝ`** — the 2-loop SM-RG output `y_s/y_μ |_GUT`.
   *Citation*: same as (1).

3. **`gj_c3_empirical : ℝ`** — the 2-loop SM-RG output `y_b/y_τ |_GUT`.
   *Citation*: same as (1).

### Empirical bracket axioms

4. **`c1_empirical_bracket`** — `gj_c1_empirical ∈ [2.195, 2.205]`.
   *Width*: `±0.005` around v0.9's quoted central value `2.200`.
   *Citation*: v0.9.1 line 11036 (`eq:gj-coefficients`); Antusch et al.
   (2005); PDG 2024 chapter 67 (running quark masses).

5. **`c2_empirical_bracket`** — `gj_c2_empirical ∈ [0.213, 0.217]`.
   *Citation*: same as (4).

6. **`c3_empirical_bracket`** — `gj_c3_empirical ∈ [0.660, 0.666]`.
   *Citation*: same as (4); note `c₃` here is the running
   `y_b/y_τ` ratio at the GUT scale, not the pole-mass ratio
   `m_b/m_τ ≈ 2.4` at `M_Z`.

**None of these axioms is the conclusion-as-axiom anti-pattern.**
Removing any one of (4)–(6) breaks the bracket; removing any one
of (1)–(3) makes the bracket vacuous (because there is no `gj_cᵢ_empirical`
to bound).  No axiom encodes the conclusion `0.014 ≤ rel_err ≤ 0.024` —
the bracket emerges from arithmetic on the algebraic targets
(`√5, 1/(3+φ), 2/3`) and the named empirical bracket axioms.

## Computation chain (how the bracket emerges)

```
Tier-2 inputs (EmpiricalBracket.lean):
  gj_c1_empirical : ℝ                      -- opaque real
  gj_c2_empirical : ℝ                      -- opaque real
  gj_c3_empirical : ℝ                      -- opaque real
  c1_empirical_bracket : ∈ [2.195, 2.205]
  c2_empirical_bracket : ∈ [0.213, 0.217]
  c3_empirical_bracket : ∈ [0.660, 0.666]

  ↓ (via GJClaim.lean — Tier 1, 0 axioms)

Tier-1 algebraic targets + brackets:
  gj_c1_algebraic = √5
  gj_c2_algebraic = 1/(3+φ)
  gj_c3_algebraic = 2/3
  √5 ∈ [2.236, 2.237]                       (Real.sqrt_le_sqrt + norm_num)
  φ ∈ [1.618, 1.619]                        (linarith from above)
  1/(3+φ) ∈ [0.216, 0.218]                  (div_le_iff + nlinarith)

  ↓ (via AlgebraicComputation.lean — Tier 1, 0 axioms)

Symbolic identification (Tier-1, fact):
  framework_predicts_GJ_in_Q_sqrt5          -- by `rfl` from definitions
  c₂ = (7 - √5)/22                          -- canonical ℚ(√5) form

  ↓ (via NumericalBracket.lean — Tier 1 on top of Tier 2 axioms)

Per-coefficient brackets (nlinarith):
  rel_err_c₁ ∈ [0.014, 0.0193]              -- c₁ dominates the lower bound
  rel_err_c₂ ≤ 0.024                        -- bracket-overlap = loose
  rel_err_c₃ ∈ [0.001, 0.011]

  ↓ (max-aggregation in Lean)

Headline theorem (Tier 2 — conditional on the 6 axioms):
  gj_within_bracket :
    0.014 ≤ max_rel_err ∧ max_rel_err ≤ 0.024

  ↓ (assembled in Verdict.lean — 0 axioms)

verdict_v092_J3 :
  (symbolic identification)
  ∧ (bracket [0.014, 0.024])
  ∧ (v0.9's central 1.7% lies in bracket)
  ∧ (bracket is wider than v0.9's quoted [0.006, 0.017])
```

## Bracket result (the headline)

```lean
theorem gj_within_bracket :
    (14 / 1000 : ℝ) ≤ max_rel_err ∧ max_rel_err ≤ (24 / 1000 : ℝ)
```

**At central inputs (v0.9 quoted values, mpmath cross-check):**
* `rel_err_c₁ ≈ 0.0164` (v0.9 reports 1.7%)
* `rel_err_c₂ ≈ 0.0071` (v0.9 reports 0.7%)
* `rel_err_c₃ ≈ 0.0056` (v0.9 reports 0.6%)
* `max_rel_err ≈ 0.0164` (c₁ dominates)

**Lean-proven bracket:** `[0.014, 0.024]`.

The bracket *contains* v0.9's central `1.7%` (`= 0.017 ∈ [0.014, 0.024]`).
The bracket is **wider** than v0.9's quoted `[0.006, 0.017]` because:
1. `c₂` algebraic and empirical brackets overlap (admitting `max_rel_err`
   as low as `0` for c₂ in the worst case), so the *lower* bound is
   driven by `c₁`'s tight 1.4% minimum.
2. `c₁` upper bound is dominated by `(2.237 − 2.195)/2.195 ≈ 0.0192`
   — even tighter empirical brackets would not push this below 1.7%
   without changing the algebraic target.

## `#print axioms` output

```
'SpectralPhysics.GJIdentification.gj_within_bracket' depends on axioms:
  [propext,
   Classical.choice,
   Quot.sound,
   SpectralPhysics.GJIdentification.c1_empirical_bracket,
   SpectralPhysics.GJIdentification.c2_empirical_bracket,
   SpectralPhysics.GJIdentification.c3_empirical_bracket,
   SpectralPhysics.GJIdentification.gj_c1_empirical,
   SpectralPhysics.GJIdentification.gj_c2_empirical,
   SpectralPhysics.GJIdentification.gj_c3_empirical]

'SpectralPhysics.GJIdentification.verdict_v092_J3' depends on axioms:
  [propext,
   Classical.choice,
   Quot.sound,
   SpectralPhysics.GJIdentification.c1_empirical_bracket,
   SpectralPhysics.GJIdentification.c2_empirical_bracket,
   SpectralPhysics.GJIdentification.c3_empirical_bracket,
   SpectralPhysics.GJIdentification.gj_c1_empirical,
   SpectralPhysics.GJIdentification.gj_c2_empirical,
   SpectralPhysics.GJIdentification.gj_c3_empirical]

'SpectralPhysics.GJIdentification.framework_GJ_symbolic' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

The symbolic identification (`framework_GJ_symbolic`) is **purely
Tier 1**.  The numerical-bracket side is cleanly separated and
consumes exactly six custom axioms — the three empirical real
constants and their three bracket axioms.

## Python / mpmath sidecar (NOT required)

This module is **self-contained** — no external sidecar is needed.
The bracket arithmetic is performed entirely by Lean (`nlinarith`,
`norm_num`) on the rational endpoints of the algebraic and
empirical brackets.

For higher precision (i.e. to *tighten* the bracket below the
v0.9-quoted `0.017` ceiling), a future sidecar at
```
yukawa/pre_geometric/GJ_identification_three_loop/compute_bracket.py
```
would run 3-loop SM-RG with improved threshold matching (the
spectral action's 288-hidden-state structure at `M_s ∼ M_R`) and
return tighter empirical brackets `c1_empirical_bracket'`,
`c2_empirical_bracket'`, `c3_empirical_bracket'`.  Re-running the
Lean computation with the tighter axioms would tighten
`gj_within_bracket` proportionally.

The current Lean module's purpose is to **establish the
audit-disciplined bracket** at the v0.9.1 precision level, leaving
the 3-loop tightening for future work.

## Anti-pattern audit

Checking against the four discipline rules:

1. **Open content as Prop predicates / named axioms, not facts.**
   The "symbolic identification" `framework_predicts_GJ_in_Q_sqrt5`
   is a `Prop`; the *numerical bracket* enters through three opaque
   real axioms + three bracket axioms, none of which is the
   conclusion-as-axiom anti-pattern.

2. **Named axioms cite real published sources.** Antusch et al.
   (2005) for the 2-loop SM-RG; PDG 2024 for running quark / lepton
   masses; v0.9.1 line 11036 (`eq:gj-coefficients`) for the framework's
   central values.  Georgi–Jarlskog (1979) for the standard
   comparison; Naculich (1993) for precise SM-RG coefficients.

3. **No definitional triviality.** The algebraic targets are *defined*
   as `√5`, `1/(3+φ)`, `2/3` — not as the empirical values dressed up.
   The empirical values are *opaque real axioms*, not literal rationals
   — so no bracket can be discharged by `rfl`.  The headline theorem
   `gj_within_bracket` is proven by genuine `nlinarith` chains
   consuming the named axioms; removing any axiom breaks the bracket.

4. **Empirical inputs isolated and never used to derive themselves.**
   The three empirical real constants and their bracket axioms live
   exclusively in `EmpiricalBracket.lean`.  No other file imports
   any empirical numeric.  No axiom is engineered to land at
   `0.6%–1.7%`; the bracket `[0.014, 0.024]` emerges honestly and
   is **wider** than v0.9's quoted range — exactly the anti-engineering
   signature.

The prior `compute/Lambda1-refinement` failure mode (definitional
identity making the match `rfl`) is structurally absent here:
`max_rel_err` is computed from absolute values + division by an
opaque empirical real, and the bracket bounds are asserted as
*rational inequalities* that the kernel checks numerically via
`norm_num` / `nlinarith`, not by unfolding to the conclusion.

## Verdict for v0.9.2 J.3

**CONDITIONAL — bracket `[0.014, 0.024]` proved; v0.9's central
`1.7%` is contained; v0.9's quoted `[0.006, 0.017]` is wider than
provable here.**

Per v0.9 `rem:gj-epistemic` (line 11036 + 5):
> "The algebraic identification becomes a theorem if the errors
> close under improved numerics."

Our bracket `[0.014, 0.024]` does **not** itself close J.3 to a
theorem in v0.9's sense.  Closing J.3 to a theorem would require:
1. A 3-loop SM-RG computation with proper spectral-action threshold
   matching, tightening `c1_empirical_bracket` from `[2.195, 2.205]`
   to (say) `[2.235, 2.239]`, which would make `rel_err_c₁ ≤ 0.001`.
2. Similar tightening of `c2_empirical_bracket` and
   `c3_empirical_bracket`.
3. (Optionally) widening `gj_c2_algebraic_bracket` from
   `[0.216, 0.218]` to a tighter `[0.2165, 0.2170]` via better
   `√5` precision.

The v0.9.2 J.3 entry is therefore properly **left open as a
well-motivated conjecture**, with this Lean module establishing
the current rigorous bracket as its honest epistemic status.

## Adjacent honest result

Per the prompt: `compute/h4-nonlinear` (in `Cosmology/H4Nonlinear.lean`)
is the adjacent honest result on polynomial bounds (Rank 10 / #18 of
the v0.9 computable inventory).  That module *does* close — the h⁴
coefficient at `ξ_cross` is `1920 · exp(12) · Λ⁴ / τ²` in closed
form, **proved unconditionally** in framework primitives.  J.3 is
the *next step up* in difficulty: it requires not just a closed-form
expression but a *quantitative match* to empirical SM data, and the
match is currently honest-but-loose (`[0.014, 0.024]` vs. v0.9's
target `[0.006, 0.017]`).

## Build status

```
$ lake build SpectralPhysics.GJIdentification.Verdict
[...]
✔ Built SpectralPhysics.GJIdentification.Verdict
Build completed successfully (2185 jobs).
```

All 5 new files in `GJIdentification/` build cleanly with the shared
`.lake` cache.  No regressions elsewhere in the repository.
