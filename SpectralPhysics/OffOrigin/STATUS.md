# `OffOrigin` — STATUS

**Scope.** The directed side's off-origin program: the C1/C2 blindness theorems
(`EtaDirIndependence.lean`) and the parity-forced second self-model deficit
(`DoddExistence.lean`; spec `dodd-existence-t1.tex`, session 2026-07-05,
handoff item P(1)).

**This directory — and the directed program — are NOT complete.** The open hinge
(`forward_origin`, the orientation ℤ/2's external origin) remains OPEN. Dodd
existence is the *negative* leg made positive-witness: records provably cannot
separate the M2 archetype pair; it does not derive the directed content's origin.

## Build wiring

| File | In root build? | Sorries |
|---|---|---|
| `EtaDirIndependence.lean` | **NO** (deliberate) | 1 (`forward_origin`, OPEN) |
| `DoddExistence.lean` | YES | 0 |

`DoddExistence.lean` deliberately does **not** import `EtaDirIndependence.lean` —
that would pull its OPEN sorry into `lake build`. The extension is mathematical,
not module-level (same precedent as the σ_P orientation branch). It DOES import
`SelfModelDeficitRigorous.SpectralZeta` (clean; for the `informationContent`
identification) and `SelfRef.GodelTrace` (clean; to cite — not modify — the
capacity-route theorem).

## Ledger — `EtaDirIndependence.lean` (unchanged by this branch)

| Result | Verdict |
|---|---|
| `spectral_functional_M2_invariant` (C1) | CLOSED given `frozen`; deriving `frozen` OPEN |
| `informationContent_M2_invariant` | CLOSED given `frozen` |
| `symmetricPart_add_antisymm` / `triple_invariant_M2_invariant` (C2) | CLOSED |
| `forward_origin` | **OPEN** (`sorry`; sharp form = ℤ/2 non-spectral selector) |

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
