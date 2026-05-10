# `compute/eta-invariant-J-self-conj` — STATUS

**Branch.** `compute/eta-invariant-J-self-conj`
**Goal.** Test whether the η-invariant of `D_F` restricted to the
J-self-conjugate `(1,1)_0` sub-block, plus a non-trivial spectral-flow
count, yields the integer 8 (the residual exponent in `y_R = τ^8`).

**Verdict.** **DEGENERATE.** The η-invariant vanishes identically on
the J-self-conjugate sub-block (Majorana pairing → exact term-by-term
cancellation, no regularisation can rescue), and the net spectral
flow vanishes identically (symmetric `0 → ±M_R` splitting). The full
APS index is 0 at the physical boundary and `−Ngen/2 = −3/2` at the
`y_R = 0` boundary. Neither is 8.

## Files

| File                                | Lines | Purpose                       |
|-------------------------------------|-------|-------------------------------|
| `EtaInvariant.lean`                 | ~190  | η ≡ 0 (Majorana pairing)      |
| `SpectralFlow.lean`                 | ~190  | Net sf ≡ 0; gross = 6 (SM)    |
| `APSIndex.lean`                     | ~210  | (η + 2·sf), bulk + boundary   |
| `Verdict.lean`                      | ~210  | DEGENERATE verdict, joint     |

Plus cherry-picked from sister branches:
* `SpectralPhysics/MajoranaSelfRef/JSelfConjugate.lean`
  (from `compute/majorana-self-reference`)
* `SpectralPhysics/IndexJSelfConj/{JSelfConjBlock,IndexComputation,
  ExponentVerdict}.lean` (from `compute/atiyah-singer-J-self-conj`)

## Tier-1 theorems (proved)

Defining all theorems in terms of `Ngen : ℕ`, `MR : ℝ`, `0 < MR`:

1. **η ≡ 0**:
   `nuR_etaInvariant_eq_zero : (nuR_spectrum Ngen MR h).etaInvariant = 0`
2. **η at every regulator s**:
   `nuR_etaSum_universally_zero : ∀ s, etaSum s = 0`
3. **No regulator gives 8**:
   `nuR_no_regularization_gives_eight : ∀ s, etaSum s ≠ 8`
4. **Net spectral flow = 0**:
   `totalNetFlow_eq_zero : totalNetFlow Ngen MR h = 0`
5. **Gross crossing count = 2·Ngen**:
   `totalGrossCrossings_eq : totalGrossCrossings Ngen MR h = 2*Ngen`
6. **Net flow ≠ 8**:
   `totalNetFlow_ne_eight`
7. **SM gross count ≠ 8**:
   `totalGrossCrossings_SM_ne_eight : totalGrossCrossings 3 MR h ≠ 8`
8. **APS pairing = 0**:
   `APS_pairing_majorana_eq_zero`
9. **APS pairing ≠ 8**:
   `APS_pairing_majorana_ne_eight`
10. **Bulk index on `S^4` = 0**:
    `bulk_S4_eq_zero`
11. **APS at `y_R = 0` boundary = `-Ngen/2`**:
    `APS_index_y_R_zero_eq`
12. **APS at physical boundary = 0**:
    `APS_index_y_R_physical_eq_zero`
13. **APS at `y_R = 0` ≠ 8** (for any `Ngen > 0`):
    `APS_index_y_R_zero_ne_eight`
14. **APS at physical ≠ 8**:
    `APS_index_y_R_physical_ne_eight`
15. **Central verdict** (all six in one):
    `central_verdict`
16. **SM verdict** (twelve-fold conjunction, including `gross = 6`):
    `SM_verdict`
17. **Joint with AS branch** (five-fold, all 0):
    `joint_with_AS_branch`

## Named axioms (Tier 3, no formalisation)

* **APS 1975** (Atiyah-Patodi-Singer Part I): η-invariant definition
  via analytic continuation of `∑ sign(λ) |λ|^{-s}` at `s = 0`.
  Used implicitly: we model η directly as the signed sum, which
  by Majorana pairing is identically zero (so the limit is 0
  unconditionally — no APS analytic-continuation lemma is invoked
  at the proof level).
* **APS 1976** (Part II): the boundary η correction in the index
  formula. Used implicitly in `APSIndex.lean`'s formulation of
  `index = bulk - (η + h)/2`.
* **Bismut-Freed 1986**: `dη/dt = 2·sf`. Used implicitly: with
  η ≡ 0 along the path, both sides are 0, so the relation is
  trivially satisfied.
* **Connes-Marcolli §15.4** (KO-dim 6 sign triple): justifies the
  Majorana pairing model — `J² = +1`, `JD = DJ`, `Jγ = -γJ` forces
  the spectral symmetry `λ ↔ -λ`.
* (Cherry-picked) `dim_Cl06_irrep_eq_eight` (Atiyah-Bott-Shapiro
  1964; Lawson-Michelsohn Theorem I.4.3).

None of these axioms is invoked as a Lean `axiom` declaration in
this branch — the η ≡ 0 result is proved at the level of the
spectral *model*, and the APS formula structure is encoded directly
in the definitions of `APS_index_y_R_zero` and `APS_index_y_R_physical`.

## Sorrys

**Zero** active sorrys in this branch's new code.

## The integer (or non-integer) η + spectral-flow gives

| Quantity                        | Value         | Equals 8? |
|---------------------------------|---------------|-----------|
| η(D_F |_{ν_R})                  | 0             | NO        |
| Net sf as `y_R : 0 → physical`  | 0             | NO        |
| Gross crossings (SM)            | 6             | NO        |
| Bismut-Freed `η + 2·sf`         | 0             | NO        |
| APS bulk on `S^4`               | 0             | NO        |
| APS boundary at `y_R = 0` (SM)  | `-3/2`        | NO        |
| APS boundary at physical        | 0             | NO        |
| Cl(0,6) module rank             | 8             | YES, but rank ≠ index |

**No combination of the η/spectral-flow data delivers 8 for the
J-self-conjugate sub-block.**

## VERDICT: DEGENERATE

### Why DEGENERATE rather than NO?

The AS branch verdict was **NO**: the AS index is 0, which is
distinct from 8 (a clean falsification — the candidate quantity
exists and we computed it).

This branch is **DEGENERATE** in the following sharper sense: the
J-self-conjugacy structure that motivated this sub-block in the
first place *forces* the η-invariant to vanish identically, with
NO regularisation freedom to extract a non-zero value. The
candidate quantity is zero by construction — there's no information
to extract. Likewise the spectral flow is zero by symmetric
splitting.

So the dispatch fails not just because the answer is wrong (0 ≠ 8)
but because **the proposed quantity is identically zero on every
J-self-conjugate spectrum** — there's no rescue available within
this framework.

### Why this route doesn't bite

Three intertwined structural reasons:

1. **Spectral pairing is built in.**  KO-dim-6's `Jγ = -γJ` forces
   `λ → -λ` on the Majorana spectrum, exactly cancelling η term-by-
   term *before* any regularisation.
2. **Net flow is built in.**  Symmetric `0 → ±M_R` splitting forces
   the net flow to be 0, with the gross count `2·Ngen` (= 6 in the
   SM, which is NOT 8).
3. **Bulk vanishes for singlet bundle.**  The same singlet structure
   that vanishes the AS index in the sister branch vanishes the
   APS bulk integral here.

Even allowing the boundary-kernel correction (`-Ngen/2`) yields a
half-integer (`-3/2` for SM), not 8.

## Build status

* `lake build SpectralPhysics.EtaJSelfConj.EtaInvariant` — green
* `lake build SpectralPhysics.EtaJSelfConj.SpectralFlow`  — green
* `lake build SpectralPhysics.EtaJSelfConj.APSIndex`      — green
* `lake build SpectralPhysics.EtaJSelfConj.Verdict`       — green
* `lake build SpectralPhysics`                            — pending
  rebuild of full root (long; mathlib downstream files); the four
  EtaJSelfConj modules and all their dependencies build cleanly.

Net additions: 4 Lean files + 1 STATUS.md (this file) + 4 lines in
`SpectralPhysics.lean` root imports. All proofs `decide`/`ring`/
`linarith`/`rw`-level — no axioms introduced beyond what was already
on the cherry-picked branches.

## Connection to prior 13 branches

| Branch                              | Result        | Bottleneck         |
|-------------------------------------|---------------|--------------------|
| `compute/majorana-block-residue`    | NEGATIVE      | Hyp B → mult 6     |
| `compute/majorana-self-reference`   | PARTIAL (τ^8) | y_R magnitude only |
| `compute/atiyah-singer-J-self-conj` | NO (= 0)      | Singlet bundle     |
| **this branch**                     | **DEGENERATE**| **η ≡ 0, sf ≡ 0**  |

The pattern: every structural integer route to "8" in the J-self-
conjugate sector either gives 0 (singlet bundle, η, sf, APS bulk)
or gives a different integer (gross crossings = 6, Cl(0,6) rank
= 8 but is a fibre dimension, not an index).

The remaining attack vectors flagged by the AS branch:
2. **ζ-function regularised dimension** `ζ_F(0; ν_R) = ?`
   (next dispatch — `compute/zetaF-prime-zero` /
   `compute/zeta-F-nuR-regularized` already started by other agents).
3. **Self-Model-Deficit refinement.** (Open.)

The standing claim after this dispatch:

> **`y_R` is transcendent IC alongside the (A.1) bit.** Two
> independent index/asymmetry routes (AS-index and η+sf) have now
> failed to derive `y_R = τ^8` structurally. The τ^8 numerical
> bracket (factor-2 fit) survives as a Tier-1 theorem in
> `MajoranaSelfRef/SelfReferenceClosure.lean`, but is not
> structurally forced.

## Cross-reference

* Sister branch (also negative, different reason):
  `compute/atiyah-singer-J-self-conj` — `IndexJSelfConj/{*}.lean`.
* Underlying numerical fit: `compute/majorana-self-reference` —
  `MajoranaSelfRef/SelfReferenceClosure.lean`.
* Foundational locus theorem: `MajoranaSelfRef/JSelfConjugate.lean`
  (`nu_R_is_unique_JSelfConj_in_16`).
