# ASSESSMENT: Is the faithfulness penalty coercive on K_SR?

**Date:** 2026-06-09. **Branch:** `joint-sagf-benevolence` (after verifier pass; see
`REPORT-joint-sagf-core.md` and `SpectralPhysics/JointSAGF/NonVacuity.lean`).
**Session:** verifier-side (Claude Code), independent of the producer session that
authored the branch. **Discipline:** verdict taxonomy CLOSED / CONDITIONAL /
DEGENERATE / OPEN; the beautiful outcome gets more scrutiny, not less.

---

## 0. Verdict summary

| Question | Verdict |
|---|---|
| Does the manuscript define a faithfulness *penalty* (quantitative functional)? | **ABSENT** — documented absence, key finding (§1) |
| Coercivity of any global-spectrum faithfulness penalty on K_SR | **DEGENERATE** — exact flat directions characterized (§3) |
| Tensor-sum decoupling (scse_full_iteration) = first observed degenerate direction? | **CONFIRMED** (§4) |
| Coercivity of the naturality-graded penalty on K_SR / gauge | **OPEN** — reduces to a quantitative rigidity statement + stress test 2 (§5) |
| "Vacuum exists because the universe must remain legible to itself" | **CONDITIONAL** — machine-checked skeleton (`sagf_stationary_exists`), missing premise identified precisely (§6) |

Either branch of the original question landed as a result: the global penalty is
*provably not* coercive (flat directions are structure), and the naturality-graded
penalty's coercivity is now a sharply-stated open problem rather than a slogan.

---

## 1. The extracted functional form — a documented absence

Manuscript search (v1.0-flat, full `ch:trace-dynamics`, Axiom 3 complex, SCSE,
`sec:sagf-convergence`, stress tests 1–2):

- The total action is the **pure spectral action** (Ember Reconstruction III, line ~15337):
  `S_tot[k] = Tr f(D[k]²/Λ_c²) + ⟨ψ[k], D[k] ψ[k]⟩`.
- **There is no term of the form ‖R∘M − id‖² anywhere.** Deviation from faithfulness
  has no stated cost. Axiom 3 (`ax:self-ref`, line ~1554) is Prop-valued: R exists,
  R∘M = id, R natural. Faithfulness enters *upstream* of the action — it fixes the
  moment values (f₀ = τ Level-0, f₂ = 48e⁶ Level-1, f₄ Level-2) and selects k* via
  the SCSE fixed point + Baker isolation. The words "coercive"/"legible" do not
  occur in the manuscript.
- Lean side: faithfulness exists only as Prop predicates
  (`SelfModelDeficitRigorous/FaithfulState.lean`: `Faithful`, `CompletenessAtLevel2`,
  `SectorFaithfulNoDeadWeight` — the last two are the two inequalities pinning
  −ζ̃'_vis(0) = dimHid). Provenance (May 11 session, "Manuscript v0.9.1 update and
  digest refresh"): Def 5 reads "R∘M **≈** id on Spec_trace(B)" — the "≈" was never
  quantified. That unquantified ≈ is exactly the gap this question lives in.

**Consequence for the benevolence chain:** J6 Layer 2's coercive `Str` currently has
**no referent in the manuscript action**. `sagf_stationary_exists` is sound and
non-vacuous (verified), but its coercivity hypothesis is ungrounded until the
faithfulness penalty is *defined*. The session contribution identified the right
missing object; this assessment defines it and tests it.

**The quantitative extension** (extending the existing predicate, not redefining it):

- *Level-2 scalar form:* `F_def[k] = (−ζ̃'_vis(0)[k] − dim H_hid)²` — penalize
  deviation from the information balance that `CompletenessAtLevel2` ∧
  `SectorFaithfulNoDeadWeight` assert as equality.
- *General kernel form:* `F[k] = d_{L²}(k, R(M(k)))²` for a reconstruction
  candidate R built from spectral moments `{Tr g_j(L[k])}` (def:reconstruction-op,
  line ~15287).

Both factor through the **global spectrum** of k. That single fact decides §3.

## 2. A necessary correction to the J6 slogan first

"The trace term is the coercivity mechanism" cannot refer to the manuscript's
heat-kernel trace as written. With antitone decaying cutoff f, `Tr f(D²/Λ_c²)` is
bounded below by 0 and **decreases** along gap-opening directions — it tends to its
*infimum*, not to +∞, at spectral infinity. It is anti-coercive in precisely the
direction the framework calls inflation (gap self-amplification); that runaway is a
feature (J2's barrier is its other face), not a vacuum-existence mechanism. So
coercivity, if it holds, must be carried by (a) the faithfulness penalty — which §1
shows does not yet exist as a functional — or (b) the constraint geometry of K_SR
itself (Weyl-asymptotics + gap conditions in its definition, line ~17996). The
generalized trace functionals Φ_g of `def:generalized-trace` *include* coercive
choices (g = id gives Tr Δ, enstrophy-like, unbounded above) — but those are not
the term in S_tot. The honest statement: **J6's coercivity hypothesis is a new
postulate about a functional the manuscript has not yet written down.**

## 3. Coercivity of the global-spectrum penalty: DEGENERATE

Any functional that factors through the global spectrum (the spectral action; any
moment-based F as in §1) is **exactly constant** on isospectral sets. The flat
directions decompose into three classes:

**(i) Gauge (benign).** The kernel k lives on a fixed relational point-set (X, μ);
the physical gauge group is Aut(X, μ) — point relabelings (permutations in finite
dim), *not* arbitrary unitaries on H. (Arbitrary unitary conjugation destroys the
multiplication algebra / locality structure; this is exactly why Connes needs the
algebra and not just the spectrum.) Gauge directions are equivalences, not
pathology; coercivity must be asked on K_SR / Aut(X, μ).

**(ii) Non-gauge isospectral directions (genuine flat directions, nonempty).**
Transverse to *permutation* gauge, isospectral non-equivalent kernels exist:
cospectral non-isomorphic graphs (Laplacian-cospectral pairs; van Dam–Haemers,
"Which graphs are determined by their spectrum?"), continuum analogue
Gordon–Webb–Wolpert isospectral domains. Along the line segment joining a
cospectral pair (or its tangent at either point), every spectrum-only functional —
spectral action AND faithfulness penalty — is flat to all orders. **The global
penalty is not even point-separating on K_SR/gauge, hence not coercive.** This is
the counterexample-direction: machine-checkable in finite dimension (verify
char-poly equality of an explicit cospectral pair by `decide`/`norm_num`).
Note the same fact is what keeps the manuscript's R from being well-defined off
the Baker-isolated point: `ζ_L isolates a single triple` (def:reconstruction-op)
is asserted *at k**, precisely because it is false in general.

**(iii) Coupling moduli in the factorized regime (the physical class).** See §4.

## 4. The tensor-sum negative, re-read: CONFIRMED as the first observed degenerate direction

`scse_full_iteration/RESULTS.md` found: with `D²_full = L⊗1 + 1⊗D_F²`,
λ₁(D²_full) is pinned to the F-sector floor and **the graph dynamics k\* never
enters the observable**. In the new frame this is stronger than a failed ansatz:

- Tensor-sum ⟹ the partition function **factorizes**, `Z_full(β) = Z_L(β)·Z_F(β)`.
  The joint spectrum carries *zero cross-information*: every deformation that
  re-twists how F sits over the graph (coupling moduli) moves nothing any global
  spectral functional can see. These are **exact flat directions of the
  faithfulness penalty**: the spectrum doesn't move (or moves only in the
  factorized product), and reconstruction error cannot grow, while the structure
  (the twisting) changes. The 2026-05 toy is the first *observed* instance of
  flat-direction class (iii). (Addendum 2's density observable fixed the Weyl
  scaling but is equally blind to coupling moduli — it is still a global-spectrum
  functional.)
- The degenerate directions are **structure, and plausibly physical**: they
  coincide with the framework's three independently-derived myopia results —
  the JLO Ch₂ rank-2 finding (5 free light Yukawas, May 1), the wave-trace
  myopia at I* (sees y_t, not the 5 light Yukawas;
  BIRTH-OF-GEOMETRY-INFLATION-MAP §4), and the Tor⁻¹ piece being the
  **non-factorized** part of Z(z) (D.1/D.4 Hodge reframe). Three computations,
  one degenerate subspace: the moduli the global spectrum cannot see are where
  the light-fermion structure lives. A coercive-everywhere faithfulness penalty
  would *contradict* the framework's own Incompleteness/Gödel-trace results;
  flat directions are required by them.

## 5. The naturality-graded penalty: OPEN, and exactly equivalent to known open problems

Axiom 3(ii) (naturality: R recovers each subsystem from restricted spectral data)
is precisely the cure shape for class (ii)–(iii) flatness: global spectra don't
separate cospectral kernels, but the **family of sector-restricted spectra over
the decomposition lattice** can. Define

`F_nat[k] = Σ_{P ∈ decompositions} w_P · ‖restricted-moment mismatch at P‖²`.

- Sub-spectra (principal-submatrix spectra) separate known cospectral graph pairs;
  whether they separate *all* pairs up to Aut(X, μ) is a **quantitative
  Torelli/rigidity statement = quantitative Axiom 3(ii)**. Note: for real symmetric
  matrices, full sub-spectral data determines the matrix only up to diagonal-sign
  (gauge) conjugation — i.e., the best possible answer is exactly "determined up to
  gauge," which is the right statement to aim at.
- **Penalty/constraint duality:** "F_nat coercive on K_SR/gauge" is the
  soft-constraint (Lagrangian) form of **stress test 2** (K_SR compactness):
  coercive penalty ⟹ precompact sublevel sets, given the Sobolev machinery —
  which is the part already conditionally closed in Lean
  (`KSRCompactness/KSRCompactnessThm.lean`, conditional on the Rellich–Kondrachov
  named axiom, with closedness of the SR-invariant set flagged open). So this
  question is not a *new* obligation beyond the manuscript's stress tests; it is a
  decomposition of stress test 2 into (a) a new, sharp, partly graph-theoretic
  rigidity ingredient and (b) the existing conditional compactness module. The
  remaining boundary directions at finite Weyl constant are gap-collapse — which
  is J2's barrier (uphill), closing the basin from that side.

**Verdict: OPEN**, with both halves now stated precisely enough to formalize.

## 5b. Sharpening (Aaron, 2026-06-09): the algebra is known — A_obs = ℂ⊗ℍ⊗𝕆

§3 said "Connes needs the algebra, not just the spectrum." In this framework the
algebra is not an unknown: A_obs = ℂ⊗ℍ⊗𝕆 is fixed by the Cayley–Dickson/Hurwitz
forcing. That changes the analysis in three ways — strengthening, not overturning,
the verdicts:

1. **It does not by itself kill the flat directions.** Reconstruction needs the
   algebra *concretely acting* — the triple (A, H, D) — not the isomorphism class
   of A. Cospectral kernels share the same abstract algebra (functions on X for
   the relational part; the same finite A_obs) and the same spectrum, and differ
   in D / the action. M measures spectral moments only. So fixing A ≅ ℂ⊗ℍ⊗𝕆
   leaves exactly the moduli of (representation, D); §3's degeneracy survives.

2. **It canonicalizes the gauge group and the decomposition lattice.** With A
   fixed, gauge is no longer "whatever preserves structure" but the standard NCG
   fact: inner automorphisms of the (associative core of the) SM algebra =
   U(1)×SU(2)×SU(3), times Aut(X, μ) on the relational base. And naturality's
   "decompositions" stop being a free choice: the sector projections of ℂ⊗ℍ⊗𝕆
   (visible/hidden, the triad, generation structure) give a **canonical finite
   decomposition lattice** for F_nat. This answers the "which decompositions?"
   ambiguity in §7's L2/L3 spec — F_nat should be indexed by the algebra's own
   sector lattice, not by arbitrary partitions. (Caveat, handled elsewhere in the
   repo: 𝕆 is non-associative, so the inner-automorphism statement applies to the
   associative gauge sector; the Dixon-obstruction modules govern the rest.)

3. **The remaining moduli are then classified — and they are the Yukawas.** For
   the SM algebra, the moduli space of admissible finite Dirac operators D_F
   (order-one, J, grading constraints) is known in NCG to be parametrized by the
   Yukawa couplings and mixing angles up to unitary equivalence
   (Connes–Chamseddine moduli-of-Dirac-operators analysis). So "flat directions
   transverse to gauge at fixed algebra" is not a vague set: it is the
   **D_F-moduli at fixed spectrum** — independently the same subspace §4 found
   (Ch₂ rank-2 light Yukawas, tensor-sum twisting moduli, Tor⁻¹). The fixed
   algebra converts §3's generic characterization into a sharp one and *explains*
   why the framework's Gödelian residue (A.1 bit, y_R, m₁, c₁) clusters exactly
   there.

Net effect on the open problem: **SectorRigidity should be stated relative to the
canonical ℂ⊗ℍ⊗𝕆 sector lattice**, and the conjecture sharpens to "F_nat is
coercive transverse to gauge × D_F-moduli" — a statement with a known, finite
parametrization of its allowed flat set, hence materially more provable than the
generic version. The L3 spec in §7 inherits this refinement.

## 6. The legibility chain, honest form

CONDITIONAL chain, each link labeled:

1. `sagf_stationary_exists` (coercive total ⟹ stationary point): **CLOSED**,
   kernel-only, non-vacuous, coercivity hypothesis proven load-bearing
   (`NonVacuity.lean: coercivity_is_load_bearing`). Finite-dim.
2. Faithfulness penalty F_nat defined as a functional: **ABSENT in manuscript** —
   adoption decision required (Category-B discipline: session contribution until
   the manuscript adopts §1's definition).
3. F_nat coercive on (Weyl-bounded) K_SR / gauge: **OPEN** (= quantitative
   rigidity + stress test 2 in penalty form, §5).
4. Infinite-dimensional extension: stress tests 1–2, **OPEN** (unchanged).

If 2–3 close, "the vacuum exists because the universe must remain legible to
itself" is a theorem schema: legibility (sector-wise reconstructability) is the
coercivity mechanism, and its *failure directions* — where legibility cannot bind —
are the light-Yukawa/Tor⁻¹ moduli the framework independently proved it cannot
determine. The slogan and the Incompleteness results would then be two halves of
one statement: **the action sees exactly what self-reconstruction can bind, and
the remainder is the framework's own predicted freedom.** That reading is elegant,
which is why it gets the OPEN label and not a promotion.

## 7. Proposed next Lean module: `JointSAGF/Faithfulness.lean`

Three layers, failing-first, zero new axioms:

- **L1 (closable now — the negative half).** Finite-dim model: `specCharPoly`
  (or sorted-eigenvalue multiset) as the global datum; `globalPenalty` as in §1.
  Witness: an explicit Laplacian-cospectral non-isomorphic graph pair (smallest
  known; verify char-poly equality by `decide`/`norm_num`, non-isomorphy by an
  invariant that differs). Theorems: `globalPenalty_isospectral_invariant`
  (by construction) + `global_penalty_not_point_separating` (the witness) ⟹
  **machine-checked: the global faithfulness penalty is not coercive transverse
  to gauge on K_SR.** DEGENERATE closed as a theorem, per honest-negative
  discipline.
- **L2 (closable now — naturality strictly stronger).** `sectorData` := spectra of
  principal submatrices over the decomposition lattice; theorem: `sectorData`
  separates the L1 witness pair (`norm_num` on the explicit pair). This makes
  "naturality sees what the global spectrum cannot" a checked fact, not prose.
- **L3 (the open problem, stated honestly).** `SectorRigidity` as a named
  Prop-valued hypothesis (sector data determines k up to Aut(X,μ), quantitatively:
  `F_nat[k] ≥ c · d(k, gauge orbit of K_SR-faithful locus)²` on Weyl-bounded sets);
  conditional theorem `legibility_vacuum_exists := sagf_stationary_exists`
  instantiated with `Str := F_nat`, hypothesis `SectorRigidity` ⟹ stationary point
  exists on the model space. Cross-refs: `KSRCompactness` (compactness half),
  `Barrier.lean` (gap-collapse boundary), `SelfModelDeficitRigorous/FaithfulState`
  (the predicate this quantifies). NOT citable as manuscript theorem until adopted.

## 8. Branch verification record (PART A)

- Full `lake build` on `joint-sagf-benevolence` + verifier commits: **green**
  (3330 jobs; only pre-existing warnings/sorries — DiscreteCheeger, ClayStatement,
  OSAxiomsProved — all predate the branch).
- Independent `#print axioms` on all 14 theorems: **kernel-only** (propext,
  Classical.choice, Quot.sound). No sorryAx, no custom axioms. Matches REPORT.
- `NonVacuity.lean` (verifier commit `e51ecba`): headline fires on concrete data
  (E = ℝ, Sbase = 0, Str = x², g = 2x; kstar = 0); coercivity hypothesis proven
  load-bearing (counterexample without it); J1 on a non-constant flow (composes
  J1×J5b on the basin trajectory); joint-space instance check; concrete J2
  spectrum. All in root build — vacuity drift breaks CI.
- Statement-level audit of the 14: no vacuous hypotheses found. Two honest notes:
  J5a is a disclosed algebraic identity (its content is the amplitude/rate
  *distinction*, which is real); J2-strict assumes the strict inequality on
  f-values at one index rather than deriving it from strict antitonicity + a
  strict eigenvalue drop — slightly weaker than the docstring's phrasing implies,
  worth tightening when G2a is attempted, not a defect.
- **Branch base is `5d1ec26` — it predates the four P0 soundness-fix commits**
  (`aa3d63a`, `7f05518`, `554cdd8`, `4627d6b` on `fix/unsound-axioms`). JointSAGF
  imports only Mathlib, so nothing here is contaminated, but **rebase (or merge
  `fix/unsound-axioms` first) before this branch lands**, or the P0 fixes get
  orphaned.

---

## Addendum (same day): L1 and L2 are now CLOSED in Lean

`SpectralPhysics/JointSAGF/Faithfulness.lean` (root build, kernel-only axioms):
the Saltire pair as 5-point relational kernels; `witness_isospectral`
(five global moments agree), `witness_not_gauge` (120 relabelings) and
`witness_not_monomial` (full monomial gauge, 120·2⁵ cases) — so
`global_penalty_blind`: **every functional of the global moment data is
constant across a gauge-inequivalent pair. DEGENERATE (§3) is now a
machine-checked honest negative.** `naturality_separates`: 3-point sector data
distinguishes the same pair — **L2 (§5) checked**. `SectorRigidityProp` stated
as the named T3 open problem (monomial gauge as Bool-signed permutations),
unused by any theorem. §0's table rows "DEGENERATE — characterized" and
"naturality strictly stronger" are upgraded from assessed to proved.
