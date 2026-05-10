# Cosmology / E-fold Multiplicity Reconciliation — STATUS

## Branch

`compute/Ne-multiplicity`

## Headline closure

**Cosmology audit P1, Tier 2 reconciliation task** (and honourable
mention #8 of `pre_geometric/computable_inventory/top10.md`):

> "v0.9 has $N_e \sim 252$ from mode activation (line 9517),
> $N_e \sim 45$ from tree potential (line 9767), $N_e = 60$ used
> in the $A_s$ closure (line 9704). At least two of these are
> wrong. The $A_s$-closure value is observationally consistent;
> the others should be retracted or relabeled."
> — `pre_geometric/cosmology_audit/triage.md`

This branch formalises the three readings as Lean definitions,
proves they are pairwise distinct, and isolates `N_e = 60` as the
canonical CMB-compatible value.  The reconciliation is not a
mathematical conjecture — it is a **documentation honesty** task:
the three readings measure different physical quantities, and only
one is the inflationary e-fold count constrained by the CMB.

## Files

| File | Role |
|------|------|
| `EfoldMultiplicity.lean` | Three `N_e` definitions, pairwise distinctness, observational-compatibility predicate, structural decomposition `252 = 288 − 36` |
| `STATUS.md` | This file |

## Theorems proved (no `True` placeholders, no `sorry`)

### `EfoldMultiplicity.lean`

1. `Ne_modeActivation = 252` — Phase 2 mode-activation count (v0.9
   line 9517).
2. `Ne_treePotential = 45` — tree-level slow-roll attractor (v0.9
   line 9767).
3. `Ne_AsClosure = 60` — CMB `A_s`-closure value (v0.9 line 9704).
4. `Ne_modeActivation_ne_treePotential` — `252 ≠ 45`.
5. `Ne_modeActivation_ne_AsClosure` — `252 ≠ 60`.
6. `Ne_treePotential_ne_AsClosure` — `45 ≠ 60`.
7. `Ne_definitions_distinct` — pairwise-distinctness conjunction.
8. `Ne_CMB_compatible` — `Ne_AsClosure = 60`.
9. `Ne_canonical_for_CMB` — `is_observationally_compatible
   Ne_AsClosure = true`.
10. `Ne_others_not_CMB_compatible` — the other two are *not*
    observationally compatible under the v0.9 closure convention.
11. `Ne_modeActivation_decomp` — `Ne_modeActivation =
    hiddenSectorDim − hiddenTopModes` (`252 = 288 − 36`).
12. `Ne_reconciliation` — bundle: pairwise-distinct ∧
    only-`60`-is-CMB ∧ `252 = 288 − 36`.

**Total: 12 theorems, 0 sorries, 0 `True`-placeholders, 0 axioms.**

## Named axioms

None *introduced by this branch*.  The three numerical values are
**v0.9-quoted constants** — the empirical/manuscript content lives
*outside* the Lean file (it is in v0.9 §"Mode Activation and the
Inflationary Clock", §"The Scalar Amplitude $A_s$ via $S_{\mathrm{top}}$",
and Remark `f4-positives`).  Lean records them as `def`s and proves
their distinctness — there is no axiom-class statement here that we
need to defer to literature.

The **observational-compatibility predicate** `is_observationally_compatible`
is a decidable `Bool` predicate that simply returns `decide (n = 60)`.
This encodes the v0.9 closure-convention identity "the CMB
`A_s`-closure value is `60`".  It is a *naming* of an empirical
fact, not a proof of it.

## Sorrys

**None.**  All four distinctness claims and the CMB-compatibility
predicate are proved by `decide` / `rfl`.

## The reconciliation: what does each `N_e` measure?

| Definition | Value | Physical content | v0.9.1 label |
|---|---|---|---|
| `Ne_modeActivation` | 252 | **Count of slow-roll mode activations.** Phase 2 of the algebra-to-geometry transition: 288 hidden modes minus 36 hidden tops which activate during the violent Big Bang Phase 1.  Dimensionally a *count*, not an e-fold. v0.9 line 9517 calls these "$\sim 252$ e-folds," but the identification "one mode activation = one e-fold" is a *naming choice*, not derived. | mode-activation count |
| `Ne_treePotential` | 45 | **Tree-level slow-roll e-fold attractor.**  The number of e-folds obtained from the tree-level potential `λ_σ = π²/(288τ) ≈ 0.124`, *before* the topological suppression `S_top` is included.  Superseded by `Ne_AsClosure` once `λ_σ = exp(−S_top)` enters. | tree-potential attractor |
| `Ne_AsClosure` | 60 | **CMB-compatible non-perturbative e-fold count.**  The unique value (modulo 11% closure tolerance) compatible with `A_s = 2 · Ch₂ · λ_σ · N_e² / π² = 2.33 × 10⁻⁹`, matching Planck 2018 `A_s^obs = 2.10 × 10⁻⁹`.  The canonical "N_e" for v0.9.1. | inflationary e-fold count |

The user's BOOM reframe (`compute/friedmann-from-sigmaTr`) ties them
together physically:

> "BOOM = slow-roll inflation phase where high-energy /
> short-wavelength modes are dense and active; lower modes
> progressively activate."

In this picture:

* the **mode-activation count** is the rate-counter on the
  hidden-light sector roll;
* the **tree-potential attractor** is the perturbative slow-roll
  estimate of how long the metric expands while that roll happens;
* the **`A_s`-closure value** is what the CMB *actually* measures
  about that expansion, after all non-perturbative corrections
  (topological factor `S_top = 28.09`) are included.

Only the third is an observable.  The other two are *internal*
quantities the framework computes en route to the observable.

## Recommendation for v0.9.1 emendation

Per the reconciliation table above:

1. **Relabel reading #1** from "$N_e \sim 252$ e-folds" to
   "**mode-activation count $N_{\mathrm{act}} = 252$**".  Phrase the
   slow-roll-attractor argument in v0.9 §"Mode Activation and the
   Inflationary Clock" without identifying $N_{\mathrm{act}}$ with
   the inflationary e-fold count.  The functional form
   $n_s = 1 - 1/(36-k)$ in the same section uses $k$, *not*
   $N_{\mathrm{act}}$, so this is a relabel-only fix.

2. **Relabel reading #2** from "$\sim 45$ e-folds" to "**tree-level
   attractor $N_e^{\mathrm{tree}} = 45$**" with an explicit
   parenthetical "(superseded by $N_e = 60$ once `S_top` is
   included)".  v0.9 already flags this implicitly at line 9762–9770;
   making it explicit closes the audit's honesty objection.

3. **Retain reading #3** as the canonical "**inflationary e-fold
   count $N_e = 60$**".  No relabel needed; only ensure §"Scalar
   Amplitude $A_s$ via $S_{\mathrm{top}}$" cites it as *the*
   canonical inflationary e-fold count, with a forward reference
   from §"Mode Activation and the Inflationary Clock" and a
   forward reference from Remark `f4-positives`.

4. **Add a one-paragraph remark** at the start of Chapter 38 (or as
   a footnote at first occurrence of "$N_e$") that reads roughly:

   > "Three quantities in this chapter share the symbol `N_e` in
   > earlier drafts: the mode-activation count $N_{\mathrm{act}} = 252$
   > (the number of light-sector modes activating during the
   > slow-roll phase), the tree-level slow-roll attractor
   > $N_e^{\mathrm{tree}} = 45$ (perturbative estimate, superseded
   > by `S_top`), and the CMB-compatible inflationary e-fold count
   > $N_e = 60$ (the value used in the `A_s` closure).  Only the
   > last is constrained by CMB observations; the others are
   > internal counting/perturbative quantities computed en route."

This is **additive documentation**, not new mathematics — the same
profile as the recommended P5 fix in `triage.md` Tier 1.

## Build status

Full `lake build` is green at HEAD of `compute/Ne-multiplicity`
(post commit, pre push).  `EfoldMultiplicity.lean` builds in 1.3 s
on top of the existing 3171-job baseline.  No regressions; no new
sorries; no new axioms.
