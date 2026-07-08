# `OffOrigin` — STATUS

**Scope.** The directed side's off-origin program: the C1/C2 blindness theorems
(`EtaDirIndependence.lean`), the σ_P orientation instrument
(`OrientationLemma.lean`, `MarkovCycle.lean`; spec `krein-orientation-lean.tex`,
companion note `krein-orientation-note.tex`, 2026-07-05), and the parity-forced
second self-model deficit (`DoddExistence.lean`; spec `dodd-existence-t1.tex`,
session 2026-07-05, handoff item P(1)).

**This directory — and the directed program — are NOT complete.** The open hinge
(`forward_origin`, the orientation ℤ/2's external origin) is now SPLIT (2026-07 tilt
probe, `ForwardOriginSplit.lean`): its matrix-level content is CLOSED, and the hinge
narrows to `loop_reads_arrow` — does the physical loop read the `sym ∘ Im`
parity-mixing channel? — which carries the file's single remaining obligation. σ_P is
the *instrument* that reads the bit given a frame, not a derivation of the frame's own
orientation. Frame-relativity is load-bearing (C′ externality made operational):
a frame-free absolute invariant reading the bit would *contradict* C′ — none is
exhibited here, and No-go 1 proves the eigenvalue route cannot supply one. Dodd
existence is the *negative* leg made positive-witness: records provably cannot
separate the M2 archetype pair; it does not derive the directed content's origin.

## Build wiring

| File | In root build? | Sorries |
|---|---|---|
| `EtaDirIndependence.lean` | **NO** (deliberate) | 1 (`loop_reads_arrow`, narrowed OPEN) |
| `ForwardOriginSplit.lean` | **YES** | 0 |
| `OrientationLemma.lean` | YES | 0 |
| `MarkovCycle.lean` | YES | 0 |
| `DoddExistence.lean` | YES | 0 |

`OrientationLemma.lean` / `MarkovCycle.lean` / `DoddExistence.lean` deliberately do
**not** import `EtaDirIndependence.lean` — that would pull its OPEN sorry into
`lake build`. The extension is mathematical, not module-level.

`ForwardOriginSplit.lean` is the exception in the OTHER direction: it is the
sorry-free, root-built half of the `forward_origin` split, and `EtaDirIndependence.lean`
imports IT (not vice versa) to state the narrowed `loop_reads_arrow` obligation in terms
of the `sym ∘ Im` read. No cycle, and no sorry enters the root build (the root does not
import `EtaDirIndependence.lean`).

`DoddExistence.lean` deliberately does **not** import `EtaDirIndependence.lean` —
that would pull its OPEN sorry into `lake build`. The extension is mathematical,
not module-level (same precedent as the σ_P orientation branch). It DOES import
`SelfModelDeficitRigorous.SpectralZeta` (clean; for the `informationContent`
identification) and `SelfRef.GodelTrace` (clean; to cite — not modify — the
capacity-route theorem).

## Ledger — `EtaDirIndependence.lean` (restructured by `feat/forward-origin-split`)

| Result | Verdict |
|---|---|
| `spectral_functional_M2_invariant` (C1) | CLOSED given `frozen`; deriving `frozen` OPEN |
| `informationContent_M2_invariant` | CLOSED given `frozen` |
| `symmetricPart_add_antisymm` / `triple_invariant_M2_invariant` (C2) | CLOSED |
| `loop_reads_arrow_implies_forward_origin` | **CLOSED** (no open hole): `LoopReadsArrow → ForwardOriginExists`, the reduction |
| `forward_origin` | **PROVED from `loop_reads_arrow`** (body has no open hole; depends on `sorryAx` only transitively via `loop_reads_arrow`) |
| `loop_reads_arrow` | **OPEN** (the file's single `sorry`; narrowed — NAMES the `sym ∘ Im` channel via `IsSymImTilt`, strictly stronger than the bare ℤ/2 non-spectral selector) |

`grep -c sorry EtaDirIndependence.lean` = **1** (the tactic on `loop_reads_arrow`;
prose no longer uses the token). The reduction `loop_reads_arrow_implies_forward_origin`
is `sorryAx`-free; `forward_origin`'s body is the application term
`loop_reads_arrow_implies_forward_origin loop_reads_arrow` (no `sorry` in the body) and
inherits `sorryAx` only transitively through `loop_reads_arrow` — i.e. the reduction is
REAL, the obligation moved, it was not renamed.

**Strict-narrowing check.** `LoopReadsArrow := ∃ sel, NonSpectral sel ∧ IsSymImTilt sel`
adds the conjunct `IsSymImTilt` (the selector factors through `symImRead = sym ∘ Im`) to
the bare `ForwardOriginExists := ∃ sel, NonSpectral sel`. The forward implication
(weakening) is proved; the reverse is NOT definitionally/trivially available (a bare
selector need not factor through `sym ∘ Im`), so `loop_reads_arrow ≢ ForwardOriginExists`.

## Ledger — Forward-origin split (`ForwardOriginSplit.lean`, `feat/forward-origin-split`, 2026-07)

Tier: finite-dimensional linear algebra / Freidlin–Wentzell action functional — **T1**.
All verdicts below CLOSED; zero `sorry`; zero new axioms; sorry-free and root-built.
Formalizes `off-origin-directed-side/quasipotential-tilt/output/forward-origin-memo.md`
and the TILTED verdict of that probe's `SUMMARY.md`.

### Part 1 — FW action degeneracy under oddness

| Result | Verdict | Statement |
|---|---|---|
| `lag_mirror` | CLOSED | odd `b` + even `D` ⇒ `Lag b D (−s) (−v) = Lag b D s v` (BOTH hyps rewritten; drop either ⇒ elaboration fails) |
| `action_mirror_invariant` | CLOSED | the FW `Action` is ℤ/2-invariant under `mirrorPath` (pointwise `lag_mirror` under the sum) |
| `degeneracy_under_oddness` | **CLOSED** | odd drift + even metric ⇒ `deltaV b D P = 0` for every instanton path — the two mirror wells are exactly degenerate |
| `degeneracy_non_vacuous` | **CLOSED (non-vacuity witness)** | exhibited `(b, D, P)` with NON-odd `b` (= the `sym ∘ Im` tilt), even `D`, and `deltaV = −2 ≠ 0`: `ΔV` is a genuine function of the free drift, not `0` by construction |

`deltaV b D P := Action b D P − Action b D (mirrorPath P)` (well-splitting along the
instanton). Load-bearing: `degeneracy_under_oddness` passes `hodd` AND `heven` on to
`action_mirror_invariant`/`lag_mirror`; removing either hypothesis fails to elaborate.

### Part 2 — the C4 extension (transpose-covariant class)

| Result | Verdict | Statement |
|---|---|---|
| `symM_isSymm` / `imPart_conjTranspose` | CLOSED (supporting) | `symM` symmetric; `Im(Kᴴ) = −(Im K)ᵀ` |
| `TransposeCovariantRead` | (predicate) | `cov`: `R Kᴴ = (R K)ᵀ` (mirror = adjoint intertwined with transpose) ∧ `hom`: `R(−K) = −(R K)` |
| `tc_read_antiHermitian_kernel_antisym` | **CLOSED** | transpose-covariant read of an anti-Hermitian kernel (`Kᴴ = −K`) ⇒ output antisymmetric `(R K)ᵀ = −(R K)` |
| `antisym_matrix_induces_odd_drift` | CLOSED (bridge) | antisymmetric read output ⇒ `inducedDrift` is odd (transpose = mirror dictionary) |
| `tc_read_tc_kernel_odd_drift` | **CLOSED** | drift-level C4: transpose-covariant read of anti-Hermitian kernel ⇒ **odd drift** ⇒ `ΔV = 0` by Part 1. The whole class cannot tilt |
| `rePart_transposeCovariant` | CLOSED (non-vacuity) | `rePart` IS transpose-covariant ⇒ `TransposeCovariantRead` inhabited, C4 theorem non-vacuous |

### Part 3 — the 2×2 archetype: `sym ∘ Im` is the tilt channel

| Result | Verdict | Statement |
|---|---|---|
| `symImRead_archetype` / `symImRead_archetype_adj` | CLOSED | `sym∘Im` of the archetype `= !![1,0;0,0]`; of its adjoint `= !![−1,0;0,0]` |
| `symImRead_not_transposeCovariant` | **CLOSED — THE SHARPEST CHECK** | `sym ∘ Im` is provably NOT transpose-covariant (fails `cov` on the archetype: `−!![1,0;0,0] ≠ !![1,0;0,0]`). So it escapes the Part-2 theorem — Parts 2 and 3 do NOT contradict |
| `archetype_drift` | CLOSED | `inducedDrift (sym∘Im archetype) = fun _ => 1` (its odd part vanishes, even part `= 1`) |
| `tilt_source_exists` | **CLOSED — WITNESS** | the `sym ∘ Im` drift is NON-odd (decidable, `norm_num`). Asserts ONLY this; no reference to the physical loop. Feeds `degeneracy_non_vacuous` |

### `#print axioms` transcript (2026-07, `lake env lean`, toolchain v4.29.0-rc6)

Every closed result in Parts 1–3, and the reduction
`loop_reads_arrow_implies_forward_origin`, depends on exactly
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no new axioms):

`lag_mirror`, `action_mirror_invariant`, `degeneracy_under_oddness`,
`degeneracy_non_vacuous`, `symM_isSymm`, `imPart_conjTranspose`,
`tc_read_antiHermitian_kernel_antisym`, `rePart_transposeCovariant`,
`antisym_matrix_induces_odd_drift`, `tc_read_tc_kernel_odd_drift`,
`symImRead_archetype`, `symImRead_archetype_adj`, `symImRead_not_transposeCovariant`,
`archetype_drift`, `tilt_source_exists`, `loop_reads_arrow_implies_forward_origin`.

`loop_reads_arrow` and (transitively) `forward_origin` depend additionally on
`sorryAx` — the single, narrowed, open obligation. `check_axioms.sh` on `OffOrigin`:
**zero `axiom` declarations** ⇒ Patterns 8/9 (unsound-axiom classes) vacuously clean.

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

## Ledger — Dodd existence (branch `feature/dodd-existence`, 2026-07-06)

Tier: everything CLOSED below is finite-dimensional linear algebra /
matrix-exponential computation — **T1**. Zero `sorry`; zero new axioms; `#print
axioms` emitted at compile time (transcript below).

### Task 1 — `RecordClass` and the inclusion lemma

| Result | Verdict | Statement |
|---|---|---|
| `specMultiset_transpose` | CLOSED | eigenvalue multiset (charpoly roots over ℂ, with multiplicity) invariant under `L ↦ Lᵀ` |
| `record_transpose_invariant` | **CLOSED** | every `RecordClass` member is transpose-invariant |
| `tracePower_transpose_invariant` | CLOSED | transpose invariance of the trace-power form, proved independently (`transpose_pow` + `trace_transpose`) — both formulations are provably transpose-invariant even before their equivalence |
| `recordClass_comp` | CLOSED | closure under post-composition of arbitrary families (capacity of the record bank never leaves the class) |
| `powerSum_one` | CLOSED | `k = 1` instance of the power-sum spectral mapping (non-vacuity evidence for the predicate below) |
| `tracePowerClass_subset_recordClass` | **CONDITIONAL** on `PowerSumSpectralMapping` | trace-power form ⊆ multiset form |
| `recordClass_subset_tracePowerClass` | **CONDITIONAL** on `PowerSumSpectralMapping` + `NewtonMultisetReconstruction` | multiset form ⊆ trace-power form |

**Newton gaps, named** (spec allows CONDITIONAL here; both predicates are TRUE
over ℂ, appear only as hypotheses, and are never asserted):

1. `PowerSumSpectralMapping` — `Tr L^k = Σ λᵢ^k`. Needs triangularization; this
   Mathlib (toolchain v4.29.0-rc6) has **no Schur triangulation**, and
   `Matrix.trace_eq_sum_roots_charpoly` covers only `k = 1`.
2. `NewtonMultisetReconstruction` — power sums determine the multiset (char 0).
   Mathlib's Newton identities exist only at `MvPolynomial` level
   (`Mathlib.RingTheory.MvPolynomial.NewtonIdentities`); the multiset-level
   transport is absent.

### Task 2 — Dodd existence

| Result | Verdict | Statement |
|---|---|---|
| `dodd_charpoly_eq` / `dodd_specMultiset_eq` | CLOSED | the archetype deformation `[[a,κ],[0,b]]` vs `[[a,0],[0,b]]` has EQUAL charpoly (`charpoly_fin_two`) — the spectrum-frozen property of C1's `M2Deformation` is here a theorem, not a hypothesis |
| `records_agree_dodd` | CLOSED | every record takes identical values on the pair (general `a, b, κ`) |
| `dodd_ne` / `dodd_directed_content` | CLOSED | the pair is distinct for `κ ≠ 0`, and differs in antisymmetric (directed) content |
| `dodd_exists` | **CLOSED** | headline: distinct 2×2 generators (corpus archetype `[[-1,1],[0,-1]]` vs `−1`) identical under EVERY `RecordClass` member |
| `record_reconstruction_impossible` | **CLOSED** | corollary: `M ∘ R ≠ id` for ANY record family (arbitrary index type = unbounded capacity) and ANY reconstruction map — parity-forced, no capacity hypothesis anywhere |
| `deficit_two_routes` | CLOSED | capacity route (`GodelTrace.godel_trace`, cited unmodified) ∧ parity route (`dodd_exists`), side by side |

### Gerrymander guard — instrument membership (spec Notes, deceptive-closure #8 watch)

`RecordClass` must provably contain the manuscript's actual instruments:

| Instrument | Verdict | Route |
|---|---|---|
| `Tr L` | **CLOSED** (`trace_mem_recordClass`) | `trace_eq_sum_roots_charpoly` |
| `det L` | **CLOSED** (`det_mem_recordClass`) | `det_eq_prod_roots_charpoly` |
| `−ζ̃'_vis(0)` (log-det form `negLogDet`) | **CLOSED** (`negLogDet_mem_recordClass`); `informationContent_eq_negLogDet` + `negZetaPrimeAtZero_eq_negLogDet` identify it with the tree's ACTUAL deficit functional (`SelfModelDeficitRigorous.SpectralZeta.informationContent`) on the diagonal realization of any `VisibleSpectrum` (multiplicities expanded on a sigma index — exact, all `mult`) | `Real.log_prod` |
| heat trace `Z(t) = Tr e^{−tL}` | **CONDITIONAL** (`heatTrace_mem_recordClass`) on `HeatTraceSpectralMapping` (`Tr e^{−tL} = Σ e^{−tλᵢ}`): TRUE (spectral mapping), not provable in this Mathlib (no Schur triangulation). Unconditional evidence: `heatTraceSpectralMapping_diagonal` (all diagonal matrices) and `heatTraceSpectralMapping_archetype` (the NON-diagonalizable dodd witness itself). | matrix exponential, `exp_add_of_commute`, square-zero series truncation |
| `I*` | **CLOSED but definitional** (`IStar_mem_recordClass`): the manuscript defines `I* = exp S(β_SR)` with `S` the *spectral* entropy, so membership is by construction — flagged as such, not passed off as substantive. The Lean tree previously had NO `I*` definition at all (only the `True := trivial` scaffold `complexity_threshold_spectral`). | by definition |

**The guard's bite** (heat trace is defined via `NormedSpace.exp`, NOT via the
spectrum): `heatTrace_blind_on_archetype` — `Tr e^{−tL}` computed from the genuine
matrix exponential on both archetype generators (the deformed one is NOT
diagonalizable) equals `2·e^t` on both, for every `t` and every `κ`. The actual
analytic instrument cannot separate the dodd pair.

**Honest flag.** General-dimension, general-matrix heat-trace membership is the
one instrument statement this Mathlib cannot close (spectral mapping for `exp` of
non-normal matrices). It is stated as the named predicate `HeatTraceSpectralMapping`
with two unconditional evidence theorems, exactly as the spec's honest-failure
clause requires. The deficit functional `−ζ̃'_vis(0)` itself — the instrument the
spec's Constraints single out — IS closed unconditionally.

### Task 3 — scaffolding replacement (`SelfRef/Consciousness.lean`)

* **Finding:** the Tier-3 scaffolding contained NO literal `True := trivial`
  named "deficit existence" — the five placeholders in `Consciousness.lean`
  (`eigenvectors_are_fixed_points`, `power_method_convergence`,
  `complexity_threshold_spectral`, `trace_unique_scalar`,
  `consciousness_requires_existence`) are OTHER Ch 8-13 claims. The
  deficit-existence claim's scaffolding status was file-level (no Lean statement
  at all). Action taken: `second_deficit_exists` (alias of `dodd_exists`,
  consciousness-word-free statement) added to the scaffolding file with a
  scaffolding-status note; **none of the five other placeholders was touched or
  reinterpreted** — no downstream statement strengthened or weakened (diff is
  purely additive plus docstring inventory).
* Bridge premises labeled at postulate level in the doc-comment of
  `second_deficit_exists`, each with the required marker "bridge premise —
  intentionally postulate-level; see handoff item P.": (1) M2-content
  identification; (2) κ-identification (handoff route P(4), open audit).

## Definition-narrowing audit (gerrymander guard, deceptive-closure #8)

1. "Eigenvalue multiset" = `charpoly.roots` over ℂ (with multiplicity) — the
   standard faithful rendering, identical convention to the σ_P branch.
2. `RecordClass` quantifies over ALL functions of the multiset (`f : Multiset ℂ
   → ℝ` unrestricted) — no continuity/measurability narrowing that could shrink
   the class.
3. Witness deviation from the spec's literal `Aᵀ = −A` phrasing, flagged: a
   nonzero antisymmetric deformation of a symmetric 2×2 `L` shifts the charpoly
   by `+κ²` (spectrum NOT frozen), so the spec's "antisymmetric AND
   upper-triangular in the eigenbasis" is satisfiable only by the corpus's
   nilpotent-in-eigenbasis archetype `[[a,κ],[0,b]]`, which the spec itself
   names. Its antisymmetric part `(κ/2)(N − Nᵀ) ≠ 0` carries the directed
   datum (`dodd_directed_content`); the frozen spectrum is proved, not assumed.
4. `dodd_exists` proved for the archetype at `κ = 1`; the general-`(a,b,κ≠0)`
   statement is `records_agree_dodd` + `dodd_ne` — broader than spec.
5. `record_reconstruction_impossible` allows an ARBITRARY index type for the
   record bank — the "independently of any capacity bound" clause is literal.
6. `I*` membership is definitional and SAID to be definitional (see guard table).

## `#print axioms` transcript (2026-07-06, `lake build`, toolchain v4.29.0-rc6)

Every result below: `depends on axioms: [propext, Classical.choice, Quot.sound]`
(no `sorryAx`, no new axioms):

`specMultiset_transpose`, `record_transpose_invariant`,
`tracePower_transpose_invariant`, `recordClass_comp`, `powerSum_one`,
`tracePowerClass_subset_recordClass`, `recordClass_subset_tracePowerClass`,
`trace_mem_recordClass`, `det_mem_recordClass`, `negLogDet_mem_recordClass`,
`informationContent_eq_negLogDet`, `negZetaPrimeAtZero_eq_negLogDet`,
`exp_eq_one_add_of_sq_eq_zero`, `heatTrace_diagonal`, `specMultiset_diagonal`,
`heatTraceSpectralMapping_diagonal`, `heatTrace_mem_recordClass`,
`IStar_mem_recordClass`, `dodd_charpoly_eq`, `dodd_specMultiset_eq`,
`records_agree_dodd`, `dodd_ne`, `dodd_directed_content`, `dodd_exists`,
`record_reconstruction_impossible`, `deficit_two_routes`,
`heatTrace_doddDeformed`, `heatTrace_doddDiag`, `heatTrace_blind_on_archetype`,
`heatTraceSpectralMapping_archetype`;
and `SpectralPhysics.Consciousness.second_deficit_exists`.
