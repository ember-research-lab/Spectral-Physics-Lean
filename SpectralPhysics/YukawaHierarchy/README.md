# YukawaHierarchy — Toward a Rigorous Derivation of `r_c/r_τ = 3/16`

**Question.** Manuscript v7 Theorem 3371 states `r_c/r_τ = 3/16 = N_c/dim(16)`
at GUT scale, verified numerically to 0.11% via two-loop RG running, but
explicitly notes (line 3398–3402) that *"a rigorous derivation from the
spectral triple axioms has not been established."*

This directory builds toward such a derivation in Lean 4 / Mathlib,
following the existing repo's three-tier epistemic convention.

---

## Epistemic structure (matches repo conventions)

| Tier | Status                          | Examples in this directory          |
| ---- | ------------------------------- | ----------------------------------- |
| 1    | Proved in Lean (0 sorry)         | Multiplicity counts in 16-spinor; SU(3)³ anomaly cancellation; equivalence `r_c/r_τ = 3/16  ⇔  y_c·dim(16) = N_c·y_τ` |
| 2    | Conditional on framework data    | Theorem A — internal integrality consistency at framework GUT values, given r_c/r_τ = 3/16 + y_t = 1 + GJ + Galois |
| 3    | Scaffolding / open               | The full 3/16 derivation itself; CCS class connection; instanton-counting hypothesis |

---

## Files (build order)

| File                          | Purpose                                                           | Status                       |
| ----------------------------- | ----------------------------------------------------------------- | ---------------------------- |
| `SO10Decomposition.lean`      | The 16-spinor decomposition under SU(3) × SU(2) × U(1)            | Tier 1 (rep-theoretic data) |
| `MultiplicityRatio.lean`      | mult(y_c)/mult(y_τ) = N_c from D_F structure                       | Tier 1 (provable)            |
| `CharmTauRatio.lean`           | r_c/r_τ = 3/16 ⇔ y_c·dim(16) = N_c·y_τ; CharmTauHypothesis class | Tier 1 equivalence + Tier 3 conjecture |
| `InstantonCounting.lean`      | y_c/y_τ = ν_total/dim(16) interpretation; ν_total = N_gen = 3      | Tier 3 conjecture            |
| `IntegralityConsistency.lean` | Theorem A — framework integrality is internally consistent         | Tier 2 conditional           |

---

## What this scaffolding does

1. **Establishes precise statements** of the framework's claims in typed
   Lean — no ambiguity about what is asserted.
2. **Proves the equivalences and rep-theoretic identities** that are
   genuinely Tier 1 (multiplicity counts, decomposition arithmetic).
3. **Records the conditional consistency** (Theorem A) — at the framework's
   self-consistent GUT values, the spectral integrality conditions all hold
   to high precision. Framework values are given as data; the consistency is
   conditional.
4. **States the open conjecture** (full derivation of 3/16) clearly as Tier 3,
   with documentation of what would close it.

## What this scaffolding does NOT do

1. Derive 3/16 from spectral triple axioms (the open question).
2. Construct the SU(3)_c gauge bundle on the manifold side.
3. Compute the Cheeger-Chern-Simons class symbolically.

These remain open for the full Path C program (~2 months of work).

## Numerical evidence (driving the formal work)

From `output/reconstruction_integrality/rigorous_C0_results.json`
(the consistency check, see `papers/spectral_physics/yukawa/` Python):

| Condition                     | Δ from integer at framework GUT |
| ----------------------------- | ------------------------------- |
| a_2 ∈ Z                        | 1.4 × 10⁻⁴                      |
| Tr(D_F⁴) ∈ Z                   | 5 × 10⁻⁸                        |
| Tr(D_F⁶) ∈ Z                   | 3 × 10⁻¹²                       |
| Tr(D_F⁸) ∈ Z                   | 0 (exact)                       |
| Galois B_l = 0, l = 1..4       | ≤ 10⁻⁹                          |
| η_lin = 0                       | 0 (exact)                       |

Theorem A formalizes this consistency.
