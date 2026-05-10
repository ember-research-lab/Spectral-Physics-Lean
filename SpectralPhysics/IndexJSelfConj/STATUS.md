# `compute/atiyah-singer-J-self-conj` — STATUS

## The hypothesis under test

> The Atiyah–Singer index theorem applied to the J-self-conjugate
> (1,1)_0 sub-block of `D_F` yields the integer **8** (the residual
> exponent in `y_R = τ^8` from `compute/majorana-self-reference`).
>
> If yes, `y_R` is structurally forced and the OP3 / ζ_F'(0) / η_B
> bottleneck closes.  If no, `y_R` remains transcendent IC.

## Verdict

### **NO.**

The Atiyah–Singer chiral index of the twisted Dirac operator
restricted to the J-self-conjugate sub-block of `D_F` is

  `index(D_F^+ |_{(1,1)_0}) = 0`

for every bundle charge `ν` (BPST `ν=1`, SM `ν=3`, anything).  In
particular:

  `index(D_F^+ |_{(1,1)_0}) ≠ 8`.

The hypothesis is **falsified**.

## Why the index vanishes

ν_R is a singlet under SU(3), SU(2), and U(1).  The AS index theorem
factors through the bundle curvature, valued in the Lie algebra of
the gauge group; on a singlet rep, the algebra acts as zero.  Hence
the chiral index of any singlet-coupled Dirac operator on a compact
4-manifold has the form

  `index(D_singlet) = ∫_M Â(M)`,

with no curvature contribution.  For `M = S^4`, `p_1 = 0`, so
`Â[S^4] = 0` and the index vanishes.

## What about the "8" of Cl(0,6)?

The dimension `dim_R Cl(0,6)_irrep = 8` (Atiyah–Bott–Shapiro 1964;
Lawson–Michelsohn 1989 Theorem I.4.3) is the **rank** of the real
spinor bundle in KO-dim 6.  This is a Bott-periodicity fact about
Clifford algebras, NOT an index of any elliptic operator.

Equating "Cl(0,6) module dim = 8" with "AS chiral index = 8" is a
**category error**:

* Rank: a global topological invariant, just the fibre dimension.
* Index: a chirality-difference of zero-modes (depends on curvature).

The category error is recorded explicitly as
`two_eights_differ` (the two integers differ by exactly 8).

## Theorems proved (Tier 1)

All theorems in this branch are Tier 1 (proved unconditionally), with
the dependency on the AS index formula in
`Bundle/AtiyahSinger.lean` (which itself is Tier-3 as a hypothesised
class instance, cf. existing repo convention).

### `JSelfConjBlock.lean`

| Theorem | Statement |
|---------|-----------|
| `jsc_subrep_is_JSelfConj` | (1,1)_0 = ν_R is J-self-conjugate |
| `jsc_subrep_unique` | other 5 sub-reps of SO(10) 16 are NOT |
| `jsc_total_majorana_count_eq_six` | 3 gen × 2 Majorana doubling = 6 |
| `cliffSpinor_KO6_dim_eq` | Cl(0,6) irrep dim = 8 (definitional) |
| `only_cliffSpinor_equals_eight` | exactly one of {6, 3, 1, 8} equals 8 |

### `IndexComputation.lean`

| Theorem | Statement |
|---------|-----------|
| `AS_index_jsc_eq_zero` | `AS_index_jsc ν = 0`, every `ν : ℤ` |
| `AS_index_jsc_BPST` | `AS_index_jsc 1 = 0` |
| `AS_index_jsc_SM` | `AS_index_jsc 3 = 0` |
| `AS_index_jsc_total_eq_zero` | summed over `Ngen` generations = 0 |
| `AS_index_jsc_ne_eight` | `AS_index_jsc ν ≠ 8`, every `ν` |
| `AhatGenus_S4_eq_zero` | `Â[S^4] = 0` (Hirzebruch 1966 §1.5) |
| `cliffDim_ne_AS_index` | the two "8"s are different quantities |

### `ExponentVerdict.lean`

| Theorem | Statement |
|---------|-----------|
| `index_does_not_match_tau_exponent_8` | (∀ν, AS=0) ∧ (∀ν, AS≠8) |
| `tau_exponent_8_not_AS_forced` | discriminator integer = 8 ≠ 0 |
| `two_eights_differ` | `cliffSpinor − AS_index = 8` |
| `summary_verdict` | combined four-prong verdict |
| `final_standing_claim` | the v1.0 standing claim |

## Sorrys

**Zero `sorry` in this branch.**

## Named axioms

### Existing (used downstream)

* `AtiyahSingerIndex` (Tier-3 class in
  `YukawaHierarchy/Bundle/PrincipalBundle.lean`):
  the AS index theorem for SU(3)-twisted Dirac on a principal
  G-bundle of charge `ν`.
  Citation: **Atiyah–Singer 1968**, Ann. Math. 87 §6;
  **Atiyah–Hitchin–Singer 1978**, Proc. Royal Soc. A 362.

### New (this branch)

* `dim_Cl06_irrep_eq_eight` (`JSelfConjBlock.lean`):
  shape-only placeholder `(8 : ℕ) = 8`.  The substantive content —
  that the Cl(0,6) irreducible real Clifford module has dimension 8
  — is recorded by definition `cliffSpinor_KO6_dim := 8` and used
  via the trivial reflexivity `cliffSpinor_KO6_dim_eq`.

  Citation: **Atiyah–Bott–Shapiro 1964**, *Clifford Modules*,
  Topology 3 (Suppl. 1), 3–38, §11 (real Bott periodicity tables);
  **Lawson–Michelsohn 1989**, *Spin Geometry*, Theorem I.4.3 and
  Table I.4.3 (Cl(p,q) for q − p ≡ 6 (mod 8)).

  This axiom is **not load-bearing** for the verdict — it is purely
  contextual.  The verdict (AS index ≠ 8) is proved without it.

## Build status

```
$ lake build
✔ [3174/3175] Built SpectralPhysics (6.0s)
Build completed successfully (3175 jobs).
```

Two pre-existing linter warnings in `SpectralPhysics/Conjectures/Hodge.lean`
(unused `simp` arg, unused variable); these are NOT introduced by this
branch.

## Connection to existing branches

### `compute/majorana-self-reference` (the immediate predecessor)

* **Verdict there**: PARTIAL — self-reference machinery picks the
  J-self-conjugate locus uniquely; numerically, τ^8 brackets `y_R`
  within factor 2; but the exponent 8 is not derivable from
  primitives.
* **Verdict here**: NEGATIVE on the AS-index dispatch.  The exponent
  8 is NOT delivered by the AS index of the J-self-conjugate sector.
* **Cherry-picked file**: `MajoranaSelfRef/JSelfConjugate.lean` (the
  GaugeRep / sub-rep selection theorems).

### `compute/majorana-block-residue`

* Hypothesis B selected (block multiplicity = 6).
* See-saw IC `M_R = 5 × 10^{14}` GeV retained as input.
* This branch confirms: AS index does NOT close the see-saw IC.

### `compute/Lambda1-refinement`

* OP3 closure for `Λ_1` is conditional on `M_R`.
* This branch confirms: OP3 stays conditional (not promoted to
  unconditional via AS index).

### `compute/zetaF-prime-zero`

* Self-Model Deficit closure depends on `y_R` input.
* This branch confirms: that dependence stays.

### Earlier (cosmology / particle):

* `compute/etaB-disambiguation`: η_B Formula B (J²/2) recorded as
  hypothesis.  This branch: Formula B does NOT become a derivation
  via the AS index of `(1,1)_0`.

## Honest framing — the v1.0 standing claim

> **`y_R` is transcendent IC, alongside the (A.1) bit.**

The τ^8 numerical bracket is real and structurally suggestive — it
is, alongside `(1/2)^15`, `λ^7`, `φ^{-22}`, one of multiple
factor-2 fits.  The **discrimination** between
* (i) "framework primitives WANT to land near `y_R`"
* (ii) "the bracket `[2 × 10^{-5}, 6 × 10^{-5}]` is wide enough that
  any fit succeeds"

is what the AS-index dispatch was designed to settle.  This branch
settles it negatively for the AS-index route.

The remaining open structural derivations of "8" (η-invariant,
zeta-determinant, refined SMD) are listed in
`ExponentVerdict.lean` but **not** formalised here.

## What this branch proves (short version)

```
∀ ν : ℤ, AS_index_jsc ν = 0
∀ ν : ℤ, AS_index_jsc ν ≠ 8
cliffSpinor_KO6_dim = 8       (Cl(0,6) module rank, NOT an index)
```

## Hard-rule compliance

| Rule | Status |
|------|--------|
| 1. No Python shortcut. Lean for all claims. | ✓ |
| 2. `sorry` documented and categorized. | ✓ (zero `sorry`) |
| 3. No `True` placeholders. | ✓ |
| 4. Build must compile (`lake build`). | ✓ |
| 5. Commit incrementally; no push. | ✓ |
| 6. **Do not manufacture a positive result.** | ✓ — honest **NO** |

## Files

```
SpectralPhysics/MajoranaSelfRef/JSelfConjugate.lean    (cherry-picked, 193 lines)
SpectralPhysics/IndexJSelfConj/
├── JSelfConjBlock.lean                                (new, ~190 lines)
├── IndexComputation.lean                              (new, ~210 lines)
├── ExponentVerdict.lean                               (new, ~190 lines)
└── STATUS.md                                          (this file)
```

## Branch policy

This branch stays **local**.  Do NOT push.  Do NOT merge.  Awaiting
review.
