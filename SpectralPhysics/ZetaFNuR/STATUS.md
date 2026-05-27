# `compute/zeta-F-nuR-regularized` — STATUS

> ⚠️ **QUARANTINED — ORPHANED & BROKEN (2026-05-26 pre-push audit).**
> This entire module chain (`JRestrictedZeta`, `ResidueAtZero`,
> `Verdict`, `ClosureRefinement`) is **NOT imported by the root
> `SpectralPhysics.lean`** (orphaned — it is excluded from the main
> `lake build`, which is why the library stays green without it) and
> **no longer compiles**: `JRestrictedZeta.lean:160` and `Verdict.lean:156`
> reference `SpectralPhysics.MajoranaBlock.three_gen_dirac_multiplicity`,
> which the `MajoranaBlock` refactor **removed** (replaced by the
> spectral-triple-valued `JSC_multiplicity`; see `MajoranaBlock/STATUS.md`).
> Porting these proofs to the new `JSC_multiplicity` API is a TODO.
> Until then the chain is dead code; the "Build succeeds" line below is
> **stale (2026-05-10)**.  NOTE: the `axiom`→`theorem` demotion of
> `zetaF_nuR_deriv_at_zero` (commit `3f66049`) is correct in *source*
> but cannot be build-verified while this chain is broken.

**Date:** 2026-05-10
**Branch:** `compute/zeta-F-nuR-regularized`
**Build:** ~~`lake build SpectralPhysics.ZetaFNuR.Verdict` succeeds
        (2438 jobs, no new errors).~~  **STALE — see quarantine note above.**

## The hypothesis under test

> The ζ-function regularization of `D_F` *restricted to the
> J-self-conjugate (1,1)_0 = ν_R sub-block* yields a structural
> integer at `s = 0` (namely `8` in the τ^8 conjecture, or some
> other forcing constant) that closes the `y_R` bottleneck.

## Verdict

### **DEGENERATE.**

The J-restricted ζ-function value at `s = 0` is *by construction*
the **multiplicity** of the (1,1)_0 sub-block in `D_F`, an integer
that is

* `mult_B = 6` under standard NCG (Connes–Marcolli §17.5,
  three-generation Dirac doubling), or
* `mult_A = 1` under a non-standard J-quotient.

**Neither equals `8`** (the τ^8 conjecture target), so the closure
`ζ_F(0; ν_R) = 8` is *not* satisfied by any NCG construction.

This is a **DEGENERATE** finding in the brief's language: the
single-block ζ-regularization at `s = 0` is *forbidden by
construction* from carrying any `y_R` information — the value at
`s = 0` is `mult · y_R^0 = mult`, an integer independent of `y_R`.

## Why DEGENERATE rather than NO?

* **NO** would mean: the J-restriction *can* yield a structural
  integer, but it isn't 8.
* **DEGENERATE** means: the very form of `ζ_F(s; ν_R) = mult · y_R^{-2s}`
  forbids it from carrying `y_R`-dependence at `s = 0`.  The only
  structural integer it can ever produce is the multiplicity itself,
  by analytic-continuation construction.

The framework's hopes for closing `y_R` via `ζ_F(0; ν_R) = N` are
misplaced: the natural slot for `y_R` is `ζ'_F(0; ν_R) = -2 mult log y_R`,
which is *exactly* what the existing `compute/zetaF-prime-zero`
branch already uses (with multiplicity 6, sector decomposition, and
see-saw cancellation via M_R fitting).

## Specific value of ζ_F(0; ν_R)

```
ζ_F(0; ν_R) = mult                          (Tier 1, this branch)

  =  6                under Hypothesis B (standard NCG)
  =  1                under Hypothesis A (non-standard J-quotient)
  ≠  8                in BOTH readings
```

The integer is **the multiplicity itself**, not a refinement of any
other integer.  It is a discrete spectral bookkeeping number, not a
derived structural constant.

## Numerical comparison

The closure equation `mult · (-log y_R) = 288 - S_charged - S_νL`
(under the hypothetical single-mode reduction) evaluates to:

| Hypothesis | mult | required `−log y_R`            | implied `y_R`       |
|------------|------|--------------------------------|---------------------|
| A (J-quot) | 1    | `-174.01`                      | `e^{174} ≈ 10^{75}` |
| B (NCG)    | 6    | `-29.00`                       | `e^{29} ≈ 10^{12}`  |
| Empirical  | -    | `+10.33`                       | `≈ 3.27 × 10⁻⁵`     |

Both NCG readings produce **negative** `−log y_R`, requiring `y_R > 1`
(unphysical Yukawa), differing from the empirical value by 80 (A) or
40 (B) orders of magnitude.

The empirical value is *consistent* with the framework's combined
see-saw closure `S_νL + S_νR = 10.61` (within 0.28), but that
identification is a **two-mode** combination (light + heavy ν), not a
single-block reduction.  See `ClosureRefinement.lean` for the
algebraic details.

## Predicted `y_R`

Under the J-restricted closure:

* **Hypothesis A** would predict `y_R ≈ 1.6 × 10^{75}`, *unphysical*.
* **Hypothesis B** would predict `y_R ≈ 4 × 10^{12}`, *unphysical*.

Neither matches the empirical `y_R ≈ 3.27 × 10⁻⁵`.  The J-restricted
ζ-function does **not** force a viable `y_R`.

## Theorems proved (Tier 1)

All theorems in this branch are Tier 1 (proved unconditionally on
top of the cited Tier-2 axioms).

### `JRestrictedZeta.lean`

| Theorem | Statement |
|---------|-----------|
| `zetaF_nuR_pos` | the J-restricted ζ is positive for `y_R > 0` |
| `zetaF_nuR_at_zero` | `ζ_F(0; ν_R) = mult` — the central degeneracy |
| `zetaF_nuR_at_zero_indep_of_yR` | value at `s = 0` does not depend on `y_R` |
| `multB_eq_NCG` | Hypothesis-B multiplicity equals the framework's NCG count |
| `zetaF_nuR_at_zero_hypA` | Hypothesis A: `ζ_F(0; ν_R) = 1` |
| `zetaF_nuR_at_zero_hypB` | Hypothesis B: `ζ_F(0; ν_R) = 6` |
| `multA_ne_eight`, `multB_ne_eight` | neither is `8` |
| `zetaF_nuR_at_zero_ne_eight` | `ζ_F(0; ν_R) ≠ 8` under both hypotheses |

### `ResidueAtZero.lean`

| Theorem | Statement |
|---------|-----------|
| `mellin_consistency` | direct evaluation matches the Mellin-transform axiom |
| `no_pole_at_zero` | the J-restricted ζ has no pole at `s = 0` (entire) |
| `residue_at_zero_is_multiplicity_only` | only the multiplicity is extractable |

### `ClosureRefinement.lean`

| Theorem | Statement |
|---------|-----------|
| `closure_RHS_eq_S_nuR` | `288 - S_charged - S_νL = S_νR` (re-arrangement) |
| `closure_RHS_decimal` | `S_νR = -174.01` (decimal form) |
| `hypA_forces_unphysical_yR` | Hypothesis A: closure forces `y_R = e^{174}` |
| `hypB_forces_unphysical_yR` | Hypothesis B: closure forces `y_R = e^{29}` |
| `J_restriction_does_not_force_viable_yR` | neither hypothesis gives viable `y_R` |
| `closure_uses_combined_seesaw` | framework actually uses `S_νL + S_νR = 10.61` |
| `empirical_consistent_with_combined` | empirical `−log y_R ≈ 10.33` ≈ `10.61` (within 0.28) |
| `J_restriction_failure_summary` | three-prong failure: 8 ≠ mult, y_R > 1, see-saw is 2-mode |

### `Verdict.lean`

| Theorem | Statement |
|---------|-----------|
| `zeta_F_nuR_verdict_degenerate` | **the headline DEGENERATE verdict**, V1+V2+V3 simultaneously |
| `cross_branch_alignment` | this branch's NO aligns with AS and majorana-block branches |
| `standing_claim_y_R_transcendent_IC` | v1.0 standing claim: `y_R` is transcendent IC |
| `headline_summary_degenerate` | clean assembly statement |

## Sorrys

**0** — every theorem is proved unconditionally on top of the cited
Tier-2 axioms.

## Named axioms (this branch's contribution)

### Newly introduced

| Axiom | File | Role | Citation |
|-------|------|------|----------|
| `mellin_finite_zeta_at_zero` | `ResidueAtZero.lean` | `ζ_F(0; ν_R) = mult` for finite spectral triple via Mellin transform | Connes–Marcolli (2008) §1.7.4 eq. (1.220); Berline–Getzler–Vergne (1992) Theorem 9.35; Hawking (1977) CMP 55, 133 |
| `zetaF_nuR_deriv_at_zero` | `ResidueAtZero.lean` | structural form `ζ'_F(0; ν_R) = -2 mult log y_R` | Connes–Marcolli (2008) §1.7.4 eq. (1.226); Hawking (1977); Ray–Singer (1971) |

### Inherited (cited but not re-introduced)

* From `compute/majorana-block-residue` (cherry-picked):
  - `J_halving_rule`, `three_generation_rule`,
    `standard_NCG_extended_Dirac`, `standard_NCG_three_generation_sum`,
    `hypothesisA_multiplicity_rule`, `hypothesisB_NCG_rule`,
    `seesaw_per_generation`.
* From `compute/zetaF-prime-zero` (cherry-picked):
  - `zeta_F_prime_at_zero_visible`, `zeta_regularization_log_sum`,
    `seesaw_product_independence`, per-sector log-Yukawa axioms.
* From `compute/atiyah-singer-J-self-conj` (cherry-picked):
  - `dim_Cl06_irrep_eq_eight` (contextual; not load-bearing).

## True placeholders

**0** — every theorem has substantive content.

## Build status

```
$ lake build SpectralPhysics.ZetaFNuR.Verdict
✔ [2438/2438] Built SpectralPhysics.ZetaFNuR.Verdict (7.7s)
Build completed successfully (2438 jobs).
```

Two pre-existing linter warnings in `SpectralPhysics/Conjectures/Hodge.lean`
and `SpectralPhysics/Algebra/Hurwitz.lean`; these are NOT introduced by
this branch.

## Connection to other branches

### `compute/atiyah-singer-J-self-conj` (sister branch)

* AS index of `(1,1)_0` = 0, not 8.
* This branch confirms: the `8` is also not extractable from the
  J-restricted ζ-function value at `s = 0`.
* **Joint verdict**: `8` is *not* an output of any standard
  spectral / index-theoretic construction on the (1,1)_0 sub-block.

### `compute/majorana-block-residue` (precursor)

* Standard NCG gives multiplicity 6 (Hypothesis B), not 1.
* This branch uses that result: `ζ_F(0; ν_R) = mult = 6`.
* **Joint verdict**: the framework's natural single-mode reading
  fails under standard NCG.

### `compute/zetaF-prime-zero` (the existing 288 closure)

* The 288 identity holds with `M_R ≈ 7×10¹⁴ GeV` fitted; the
  see-saw cancellation gives `S_νL + S_νR = 10.61`.
* This branch confirms: the J-restriction does **NOT** improve on
  this — the `s = 0` slot is the multiplicity, the `s ↦ 0` derivative
  is just the existing `−12 log y_R` ν_R log-sum (Hypothesis B).
* **Joint verdict**: `M_R` remains a fitted parameter; `y_R` is
  transcendent IC.

### `compute/Lambda1-refinement`

* OP3 closure for `Λ_1` is conditional on `M_R`.
* This branch confirms: that conditionality persists.

## Honest framing — the v1.0 standing claim

> **`y_R` is transcendent IC.**

Three independent attack vectors have now returned negative or
degenerate verdicts:

1. **AS index** (`compute/atiyah-singer-J-self-conj`):
   `index(D_F^+ |_{(1,1)_0}) = 0`, not 8.
2. **NCG multiplicity** (`compute/majorana-block-residue`):
   standard NCG forces `mult = 6`, not 1.
3. **ζ-restricted residue** (this branch):
   `ζ_F(0; ν_R) = mult ∈ {1, 6}`, neither equals 8.

None of the three deliver the integer 8 expected by the τ^8
conjecture.  The numerical bracket `y_R ≈ 3.27 × 10⁻⁵` ↔
`τ^8 ≈ 4.4 × 10⁻⁵` (factor-2 fit) is real and structurally
suggestive, but NOT *forced* by the framework's primitives.  The
framework's standing position — that `y_R` is fitted, not derived —
holds.

## Hard-rule compliance

| Rule | Status |
|------|--------|
| 1. No Python shortcut. Lean for all claims. | yes |
| 2. `sorry` documented and categorized. | yes (zero `sorry`) |
| 3. No `True` placeholders. | yes |
| 4. Build must compile (`lake build`). | yes |
| 5. Commit incrementally; no push. | yes |
| 6. **Do not manufacture a positive result.** | yes — honest **DEGENERATE** |

## Files

```
SpectralPhysics/ZetaFNuR/
├── JRestrictedZeta.lean        ~211 lines
├── ResidueAtZero.lean          ~186 lines
├── ClosureRefinement.lean      ~261 lines
├── Verdict.lean                ~213 lines
└── STATUS.md                   this file
```

Total: 4 Lean files, 1 status file, ~870 lines of Lean.

## Branch policy

This branch stays **local**.  Do NOT push.  Do NOT merge.  Awaiting
review.

## What this branch proves (short version)

```
∀ mult : ℕ, ∀ y_R > 0, zetaF_nuR mult y_R 0 = mult     (Tier 1)
multA = 1, multB = 6                                    (Tier 1)
multA ≠ 8 ∧ multB ≠ 8                                   (Tier 1)
∀ y_R > 0, zetaF_nuR multA y_R 0 ≠ 8                    (Tier 1)
∀ y_R > 0, zetaF_nuR multB y_R 0 ≠ 8                    (Tier 1)
288 - S_charged - S_nuL = S_nuR                         (Tier 1)
S_nuL + S_nuR = 10.61                                   (Tier 1)
J-restricted closure forces y_R > 1 (unphysical)        (Tier 1)
```
