# `OffOrigin` — STATUS

**Scope.** The directed side's off-origin program: the C1/C2 blindness theorems
(`EtaDirIndependence.lean`) and the σ_P orientation instrument
(`OrientationLemma.lean`, `MarkovCycle.lean`; spec `krein-orientation-lean.tex`,
companion note `krein-orientation-note.tex`, 2026-07-05).

**This directory — and the directed program — are NOT complete.** The open hinge
(`forward_origin`, the orientation ℤ/2's external origin) remains OPEN; σ_P is the
*instrument* that reads the bit given a frame, not a derivation of the frame's own
orientation. Frame-relativity is load-bearing (C′ externality made operational):
a frame-free absolute invariant reading the bit would *contradict* C′ — none is
exhibited here, and No-go 1 proves the eigenvalue route cannot supply one.

## Build wiring

| File | In root build? | Sorries |
|---|---|---|
| `EtaDirIndependence.lean` | **NO** (deliberate) | 1 (`forward_origin`, OPEN) |
| `OrientationLemma.lean` | YES | 0 |
| `MarkovCycle.lean` | YES | 0 |

`OrientationLemma.lean` / `MarkovCycle.lean` deliberately do **not** import
`EtaDirIndependence.lean` — that would pull its OPEN sorry into `lake build`.
The extension is mathematical, not module-level.

## Ledger — `EtaDirIndependence.lean` (unchanged by this branch)

| Result | Verdict |
|---|---|
| `spectral_functional_M2_invariant` (C1) | CLOSED given `frozen`; deriving `frozen` OPEN |
| `informationContent_M2_invariant` | CLOSED given `frozen` |
| `symmetricPart_add_antisymm` / `triple_invariant_M2_invariant` (C2) | CLOSED |
| `forward_origin` | **OPEN** (`sorry`; sharp form = ℤ/2 non-spectral selector) |

## Ledger — σ_P orientation instrument (branch `feature/krein-orientation`, 2026-07-06)

Tier: everything below is finite-dimensional linear algebra — **T1**.
All verdicts CLOSED; zero `sorry`; zero new axioms. `#print axioms` emitted at
compile time by both files (see transcript below): every closed lemma depends on
exactly `[propext, Classical.choice, Quot.sound]`.

### Task 1 — No-gos (`OrientationLemma.lean`, general finite dimension)

| Result | Verdict | Statement |
|---|---|---|
| `antisymm_charpoly_roots_neg` | CLOSED | core: `Mᵀ = −M` (over ℂ) ⇒ charpoly-roots multiset = its negation |
| `skew_hermitization_spec_symmetric` | CLOSED | spec of `i•A` symmetric under negation (`A` real antisymmetric); No-go 1 |
| `skew_plain_signature_zero` | CLOSED | plain Krein signature of `i•A` ≡ 0 (via `rootsSignature`, #pos − #neg roots) |
| `pfaffian_odd_dim_zero` | CLOSED | `det A = 0`, odd dim; Pfaffian corollary in docstring only (Mathlib has no Pfaffian API; det carries the odd-dim content — per spec, no Pfaffian theory built) |
| `hermitize_isHermitian` | CLOSED (supporting) | `i•A` is genuinely Hermitian |

### Task 2 — 3×3 orientation lemma (`OrientationLemma.lean`, fully concrete)

Locked sign conventions (note, in-session): `σ_P(H) := sign(Im tr(P3ᵀ * H))`;
`H(a,b,c) = a•1 + b•(P3+P3ᵀ) + (I·c)•(P3−P3ᵀ)`; with these `σ_P = sign c`.

| Result | Verdict | Statement / achieved generality |
|---|---|---|
| `circulant_eigenvalues` | CLOSED | `charpoly H(a,b,c) = ∏ₖ (X − λₖ)`, `λₖ = a + 2b·cos(2πk/3) − 2c·sin(2πk/3)` — exactly the note's formula (charpoly-factorization route; certificate `linear_combination` on `I² = −1`, `(√3)² = 3`) |
| `circulant_roots` | CLOSED | roots multiset = `{λ₀, λ₁, λ₂}` |
| `multiset_blind_to_sign` | CLOSED | spec `H(a,b,−c)` = spec `H(a,b,c)`, proved at *polynomial* level via `H(a,b,c)ᵀ = H(a,b,−c)` (`Hmat_transpose`) — the chamber flip IS the transpose; Fourier-relabeling witness visible in `circulant_roots` |
| `sigma_reads_sign` | CLOSED | `σ_P(H(a,b,c)) = sign c` (`Im tr(P3ᵀH) = 3c`, `trace_pairing`) |
| `sigma_transpose_odd` | CLOSED — **broader than spec**: proved for every Hermitian 3×3 `H`, not just the circulant family (family corollary `sigma_transpose_odd_circulant`) |
| `sigma_symmetric_stable` | CLOSED — **broader than spec**: σ_P unchanged by adding *any* real 3×3 matrix (symmetry not needed; real content cannot enter `Im tr`). Load-bearing circulant-symmetric case: `sigma_circulant_symmetric_stable` |
| `spectrum_at_note_point`, `note_lambda_brackets` | CLOSED (numeric anchor) | exact spectrum `{1.7, 0.65 ± √3·0.6}` at `(1, 0.35, 0.6)` + rational brackets `(−0.39, −0.38)` / `(1.68, 1.69)` matching the note's `{−0.389…, 1.689…, 1.7}` |

`#eval`/`decide` numeric check: **not done** — obstructed by noncomputable ℝ
(`Real.sqrt`/`Real.sin`/`Real.sign` carry no executable code). Replaced by the
proved exact values + brackets above (spec explicitly allows this with report).

### Task 3 — n=3 detailed balance / cycle current (`MarkovCycle.lean`, over ℝ)

| Result | Verdict | Statement |
|---|---|---|
| `detailed_balance_iff_symm` | CLOSED | `k_f = k_b` ⟺ `Wᵀ = W` ⟺ `antisymmetricPart W = 0` |
| `detailed_balance_iff_sigma_zero` | CLOSED | fourth equivalent of the note: db ⟺ `σ_P = 0` |
| `sigma_eq_current_sign` | CLOSED — **broader than spec**: no `k_f ≠ k_b` hypothesis needed (both sides 0 at db) | `σ_P(W) = sign(k_f − k_b)` (real form `sign tr(Rᵀ A)`, `tr(RᵀR) = 6`) |
| `markovGen_transpose`, `markovGen_antisymmetricPart`, `trace_Rr_pairing` | CLOSED (supporting) | |

General-`n` cycle-current statement: **OPEN** (promotion target; which cycle's
frame — specced separately).

## Definition-narrowing audit (gerrymander guard, deceptive-closure #8)

**No definition was narrowed from the note's version.** Deviations are all
*broadenings* or convention-faithful choices, flagged here:

1. `sigma_transpose_odd`: proved for all Hermitian `H` (note states it for the
   circulant family) — broader.
2. `sigma_symmetric_stable`: proved for all real perturbations (note: real
   symmetric) — broader; symmetry is genuinely unnecessary in the Hermitian
   convention, where antisymmetric content sits in the imaginary part.
3. `sigma_eq_current_sign`: hypothesis `k_f ≠ k_b` dropped — broader.
4. "Eigenvalue multiset" formalized as `charpoly.roots` (with multiplicity, over
   ℂ; charpoly splits, so card = dim) — the standard faithful rendering.
5. `rootsSignature` counts roots by sign of real part; for the Hermitian matrices
   at issue all roots are real (`hermitize_isHermitian`), so this is the usual
   signature — not a narrowing.
6. No-go 2 formalized as the determinant statement per spec; the Pfaffian
   corollary is docstring-level (Mathlib gap: no Pfaffian API), NOT claimed as a
   formalized result.
7. Markov generator: uniform-rate 3-state chain per spec ("keep the symmetrized
   conjugation trivial at this tier") — the note's general-π symmetrization is
   part of the OPEN general-`n` promotion, not silently claimed.

## `#print axioms` transcript (2026-07-06, `lake env lean`, toolchain v4.29.0-rc6)

Every lemma below: `depends on axioms: [propext, Classical.choice, Quot.sound]`
(no `sorryAx`, no new axioms):

`antisymm_charpoly_roots_neg`, `skew_hermitization_spec_symmetric`,
`skew_plain_signature_zero`, `pfaffian_odd_dim_zero`, `hermitize_isHermitian`,
`circulant_eigenvalues`, `circulant_roots`, `multiset_blind_to_sign`,
`sigma_reads_sign`, `sigma_transpose_odd`, `sigma_transpose_odd_circulant`,
`sigma_symmetric_stable`, `sigma_circulant_symmetric_stable`,
`spectrum_at_note_point`, `note_lambda_brackets`,
`markovGen_transpose`, `markovGen_antisymmetricPart`, `detailed_balance_iff_symm`,
`trace_Rr_pairing`, `sigma_eq_current_sign`, `detailed_balance_iff_sigma_zero`.
