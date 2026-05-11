# compute/faithfulness-forces-yR — STATUS

**Branch**: `compute/faithfulness-forces-yR`
**Date completed**: 2026-05-10
**Build**: `lake build` returns success (3178 jobs).
**Sorries in this directory**: 0.
**Axioms in this directory**: 0.

## TL;DR

**Combined verdict: NO across all five readings A / B / C / D / E.**

Axiom 3 (Spectral Faithfulness) — in any of its standing readings —
does not pin the Majorana Yukawa coupling `y_R` at the J-self-conjugate
locus `(1,1)_0`.  This consolidates the **transcendent-IC framing**
for `y_R` as the genuinely-supported v1.0 standing claim.

This is the fifth honest negative on the `y_R`-from-(1,1)_0 question:

| Route | Branch | Verdict |
|-------|--------|---------|
| Atiyah–Singer | `compute/atiyah-singer-J-self-conj` | NO (η-AS index = 0 at J-self-conj) |
| ζ_F(0) | `compute/zeta-F-nuR-regularized` | DEGENERATE (single-eigenvalue collapse) |
| Self-Model Deficit (J-fixed) | `compute/self-model-deficit-J-fixed` | NO (closure for any `y_R > 0`) |
| η + Spectral Flow | `compute/eta-spectral-flow` | NO (vanishes at J-self-conj) |
| **Axiom 3 (this branch)** | `compute/faithfulness-forces-yR` | **NO across A/B/C/D/E** |

## Theorems proved

### Reading A — Trivial reconstruction (`AxiomThreeRestricted.lean`)

Pre-existing partial work.  All theorems Tier 1, sorry-free.

* `axiom_three_faithful_at_every_yR` — finite-dim spectral
  determination is automatic for every `y_R ≥ 0`.
* `yR_recovery_correct` — `yR_recovered (y_R · v) v = y_R`.
* `reconstructibility_faithful_set` — recovery succeeds on `(0, ∞)`.

**Verdict A: DEGENERATE.**

### Reading B — CD-tower extension (`CDTowerExtension.lean`)

* `cdTower_length_eq_four` / `cdTower_max_eq_eight` — Hurwitz tower
  has four levels capping at 𝕆.
* `termination_invariant_is_natural` — *every* CD-tower invariant
  takes natural-number values (typing).
* `termination_invariant_misses_irrational` — for any `φ`, the real
  `(φ cdTowerDims) + 1/2` is positive and not equal to `(φ cdTowerDims)`.
* `CD_tower_at_majorana_does_not_force_yR` — for every claimed
  termination invariant `φ`, the universally-quantified statement
  "`(φ cdTowerDims : ℝ) = y` for every `y > 0`" is false.
* `CD_tower_invariant_cannot_equal_non_natural_yR` — naturals miss
  irrationals; in particular the empirical `y_R ≃ 3.27e-5`.

**Verdict B: NO** — discrete termination invariants cannot pin a
continuous coupling.  Faithfulness, as it acts through `thm:forcing`,
is integer-valued.

### Reading C — Composition theorem on JSC (`CompositionFaithfulness.lean`)

* `jscSpectrumList_length` / `jscSpectrumList_const` — JSC spectrum
  is the constant list of length 6.
* `compositeSpectrum_length` — `|S_jsc ⊞ S_vis| = 6 + |S_vis|`.
* `compositeSpectrum_injective_in_yR` — distinct `y_R` give distinct
  composites (proved via `List.head?`).
* `composition_faithful_at_every_yR` — every `y_R ≥ 0` produces a
  faithful composite.
* `composition_faithfulness_does_not_force_yR` — joint statement:
  both compositions faithful, both distinct.
* `composition_has_no_preferred_yR` — for every claimed `y_R*`,
  `y_R* + 1` is also faithful.

**Verdict C: NO** — additive convolution + faithfulness is preserved
across the *entire* positive-`y_R` axis.  The "uniqueness" of the
composition theorem is uniqueness of the *operation* (`⊞`), not of
the *operand* (`y_R`).

### Reading D — Operator reconstruction (`OperatorReconstruction.lean`)

* `jscDiracOperator_distinct_at_distinct_yR` — distinct `y_R` give
  distinct constant-scalar operators.
* `J_commutes_with_jscDiracOperator` — J is the identity on (1,1)_0,
  so it commutes with any constant operator.
* `gamma_commutes_with_jscDiracOperator` — γ-grading commutes with
  any constant scalar operator.
* `order_one_satisfied_at_every_yR` — order-one condition trivially
  satisfied (a single eigenvalue makes inner commutators zero).
* `operator_reconstruction_does_not_force_yR` — for *every* `y_R > 0`,
  the operator satisfies (i) scalar form, (ii) J-self-conjugacy,
  (iii) order-one.
* `operator_reconstruction_admits_continuum_of_yR` — distinct `y_R`
  produce distinct, equally reconstruction-compatible operators.

**Verdict D: NO** — same structural pattern as the four prior
standard-machinery routes: J-self-conjugacy that *selects* the locus
also commutes with every constant scalar, so cannot single out one.

### Reading E — Self-Model Deficit + Faithfulness (`SelfModelDeficitFaithfulness.lean`)

* `jsc_eigenvalue_eq_majorana_scale` — `λ_JSC = M_R = y_R · v_R`.
* `visibleSpectrum_independent_of_yR` — visible spectrum is constant
  in `y_R` (typing).
* `closure288_holds_at_every_M_R` — the `-ζ'_vis(0) = 288` value is
  derivable for every `M_R` (the value is `M_R`-independent in the
  standing formalisation).
* `closure288_does_not_pin_M_R` — closure satisfied at any pair.
* `self_model_deficit_faithfulness_does_not_force_yR` — joint
  faithfulness-plus-closure satisfied at every `y_R`.
* `reading_E_admits_continuum_of_yR` — both readings simultaneously
  satisfied at any pair.

**Verdict E: NO** — closure is constant in `M_R`; faithfulness on
visible algebra is independent of JSC scale.  Reproduces the prior
negative of `compute/self-model-deficit-J-fixed`.

### Combined Verdict (`Verdict.lean`)

* `axiom3_yR_verdict` — for every `y_R ≥ 0`, all four sorry-free
  per-reading conditions hold simultaneously.
* `axiom3_admits_continuum_of_yR` — any pair of distinct positive
  `y_R` jointly satisfies the readings while remaining distinct
  *as operators*.
* `axiom3_yR_verdict_NO_across_all_readings` — packaged conjunction
  of the per-reading negatives.

## Named axioms with citations

This dispatch introduces **zero new axioms**.  It cites:

* **v0.9 Axiom 3 (`ax:self-ref`, line 299)** — Spectral Faithfulness.
* **v0.9 `thm:forcing`** — Hurwitz / CD termination at 𝕆.
* **v0.9 line 6731** — first-order condition for Dixon algebra
  ("principal open problem").
* **v0.9 line 16783** — composition theorem (currently flagged
  hand-wavy in manuscript).
* **Connes–Marcolli ζ-regularisation** (Connes-Marcolli 2008 §15.4) —
  cited for context, not invoked.
* `SpectralPhysics/Axioms/SelfRefClosure.lean` `SpectralDetermination`
  — typeclass formalisation.
* `SpectralPhysics/Algebra/Forcing.lean` `tower_terminates_by_zero_divisors`
  — termination at 𝕆.
* `SpectralPhysics/SelfRef/SelfModelDeficit.lean` `zeta_visible_value`,
  `deficit_eq_dark` — 288 closure.

## Sorries categorized

**None** in this directory.  All Tier 1.  No `True` placeholders.

## Per-reading verdict summary

| Reading | Mechanism | Verdict |
|---------|-----------|---------|
| A | Trivial reconstruction | **DEGENERATE** |
| B | CD-tower / Hurwitz termination | **NO** (integer vs real) |
| C | Composition theorem (additive convolution) | **NO** (parametric continuity) |
| D | Full Axiom 3 (operator reconstruction) | **NO** (gauge-invariance) |
| E | Self-model deficit + faithfulness | **NO** (closure is M_R-independent) |

**Combined: NO.**

## Consequences for the framework

* **OP3 status**: remains conditional on input `M_R` (Hypothesis B).
* **ζ_F'(0) closure**: remains a fitted constraint, not a derivation.
* **η_B Formula B**: remains a phenomenological formula.
* **`y_R` standing**: enters as input data (transcendent IC).
* **v1.0 manuscript framing**: Axiom 3 alone, in any standing reading,
  cannot serve as the missing constraint that closes `y_R`.  The
  honest framing is transcendent IC.

## Build status

```
$ lake build
Build completed successfully (3178 jobs).
```

The five new files in `SpectralPhysics/FaithfulnessForcesYR/` plus
the imported `SpectralPhysics/MajoranaSelfRef/JSelfConjugate.lean`
contribute zero sorries, zero axioms, and no `True` placeholders to
the workspace.

## Cross-references

* `SpectralPhysics/MajoranaSelfRef/JSelfConjugate.lean` — J-self-conj
  uniqueness theorem; ν_R is the unique JSC sub-rep of SO(10) `16`.
* `SpectralPhysics/Axioms/SelfRefClosure.lean` — Axiom 3 typeclass.
* `SpectralPhysics/Algebra/Forcing.lean` — `thm:forcing`, termination
  at 𝕆.
* `SpectralPhysics/SelfRef/SelfModelDeficit.lean` — 288 closure.
* `compute/atiyah-singer-J-self-conj` — first standard-machinery NO.
* `compute/zeta-F-nuR-regularized` — second.
* `compute/self-model-deficit-J-fixed` — third.
* `compute/eta-spectral-flow` — fourth.
* **This branch** — fifth, climbing to Axiom 3 directly.
