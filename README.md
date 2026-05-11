# Spectral Physics: Lean 4 Formalization

A machine-checked formalization of the spectral physics framework
(`papers/spectral_physics/spectral-physics-v0.9.1.tex`), built under
adversarial audit discipline. The repository pairs Tier-1 proofs of the
core spectral apparatus with **honest predicate-hypothesis closures** of
v0.9's open problems, and **catalogued negative results** for hypotheses
that do not survive Lean-level scrutiny.

Part of [**Ember Research Lab**](https://ember-research-lab.github.io/) —
independent research deriving geometry, quantum mechanics, and consciousness as
three projections of the graph Laplacian. See the [concepts
index](https://ember-research-lab.github.io/concepts.html) for definitions of
the framework's terms.

**169 Lean files | 28 top-level modules | ~15 sorry sites | 54 named declarations carrying axiom-class status**

Builds against Lean 4.29.0-rc6 and Mathlib master via `lake build`
(3179 jobs at last full pass, 2026-05-10).

---

## Audit Discipline

Every closure in this repository follows four rules, established after an
adversarial audit caught seven deceptive prior closures (see "Redemption
History" below):

1. **Open content travels as named `Prop` predicate hypotheses**, not as
   asserted facts. A conditional theorem reads
   `theorem T (h : P) : Q` where `P` is the open content stated as a
   predicate; the theorem produces `Q` *given* `P`, not by deriving `P`.
2. **Named axioms cite real published literature as general facts.** They
   are not numerical constants engineered to land on a target sum, and
   they are not framework-specific identities dressed up as standard
   results.
3. **No definitional triviality.** If a theorem of the form `n = m`
   between two definitions discharges by `rfl` because both unfold to
   the same numeral, that is flagged in the directory's `STATUS.md` and
   replaced by a predicate-over-spectral-triple formulation where the
   integer *emerges* via a rewrite chain that breaks if any named
   axiom is removed.
4. **Empirical inputs are isolated and labelled.** They are never used
   to derive themselves; a number like `Λ_obs` enters as a single
   `Tier-2` axiom and is consumed once.

Each `compute/*` branch carries a `STATUS.md` recording: which theorems
are Tier 1 (proved), which named axioms it introduces (with citation),
which predicates carry open content, and the explicit verdict —
**CLOSED / CONDITIONAL / OPEN / DEGENERATE / NO**.

---

## Tiered Status of Results

### Tier 1 — Proved in Lean (zero `sorry`, zero open hypotheses)

Core spectral apparatus:

- **Lattice spectral gap** — connected relational structure with `L ≥ 0`
  implies `λ₁ > 0`; null space = constants (`Laplacian.lean`).
- **Heat kernel** — `e^{-tL}` is PSD (reflection positivity); exponential
  correlator decay at rate `λ₁` (`HeatSemigroup.lean`).
- **Rayleigh / Courant-Fischer** — variational characterization
  `R(v_k) = λ_k`, min-max principle (`RayleighQuotient.lean`).
- **Bakry-Émery on graphs** — discrete `CD(κ, ∞)`, Lichnerowicz
  `κ ≤ λ₁`, SU(2) bound `ρ_0 = 12/7` (`BakryEmery.lean`).
- **Cheeger-Colding convergence** — antitone + bounded-below sequences
  converge; the gap passes to the limit via `ge_of_tendsto`
  (`CheegerColding.lean`).
- **Wick rotation** — analytic continuation of `Z(β)`, equal-time
  commutator vanishing, spacelike correlator decay (`WickRotation.lean`).
- **Cayley-Dickson tower** — `ℝ → ℂ → ℍ → 𝕆` with norm-multiplicativity
  (`CayleyDickson.lean`, `Hurwitz.lean`).
- **Numerical predictions** — `α_s = π(2+φ)/96` (0.4%), Cabibbo
  `(150 − 23√5)/440` (0.12%), `T_c/v` (0.6%), `θ_13`, `δ_CP`
  (`Predictions/`).
- **Self-reference** — Gödel trace; `ε̄ ≥ I·C_min/τ`
  (`SelfRef/`, `accuracy_integration_tradeoff`).
- **YukawaHierarchy** — 16-file SO(10) instanton-counting scaffold
  closed at the Tier-1 boundary; `main_yukawa_ratio_theorem`,
  `mult(y_c)/mult(y_τ) = N_c`, BPST self-duality, anomaly cancellation
  for any ν (`YukawaHierarchy/`).

### Tier 2 — Conditional on named, standard, unformalized results

These theorems are **proved in Lean** given explicit hypotheses naming
classical theorems. The conclusions are honest; the hypotheses are the
inputs whose Lean-level formalization is deferred.

- **Continuum mass gap** — `assembly_clay_v3 : … h_antitone : … →
  ∃ m, m > 0 ∧ (N : ℝ)/4 ≤ m²`. The eigenvalue antitone property
  for lattice refinements is hypothesised, not proved.
- **OS axioms in continuum** — OS2/OS3 transfer with 0 sorry; OS4
  clustering has one residual `sorry` for a `Finset.sum` splitting at
  `k = 0`.
- **Lattice Lichnerowicz gap values** — `3/4` for SU(2), `6/7` for
  SU(3), etc., are supplied as data on `CompactSimpleGroup`; the
  O'Neill formula `Ric(A/G) ≥ N/4` is cited, not formalized.
- **SeeleyDeWitt `R²` coefficient** — sign-triple independence is
  **unconditional Tier 1**; per-DOF normalization is **conditional on a
  cutoff-rescaling axiom** explicitly named and flagged (see
  `SeeleyDeWitt/STATUS.md`, redemption rewrite 2026-05-10).
- **Friedmann from `σ_tr`** — `friedmann_from_sigmaTr` proved given the
  Whitt-1984 / De Felice-Tsujikawa-2010 conformal-frame transform
  carried as an axiom-class declaration (`Cosmology/STATUS.md`).
- **κ₂ to 0.01-unit precision** and **`f₄` via Edgeworth tower** —
  closed-form coefficient at `ξ_cross` (Rank 10 / #18 of the v0.9
  computable inventory), with the Edgeworth expansion's regularity
  hypothesis named (`OP3/STATUS.md`).

### Tier 3 — Scaffolding (structure without full mathematical content)

- **Wightman axioms W1–W5** carried as bare `Prop` fields on
  `OSReconstruction.WightmanData`; the genuine spectral content lives
  in Tiers 1/2.
- **Wightman distributions** — `wightman_n := fun _n => sorry` in
  `ClayStatement.lean`. OS reconstruction (Osterwalder-Schrader
  1973/1975) is cited, not formalized.
- **GR / Spacetime** — placeholder theorems (`: True := trivial`) for
  spacetime emergence and dimension running.
- **Consciousness** — definitional statements as `True := trivial`;
  these are spectral definitions, not empirical claims.

### Honest negatives — what *did not* close

Five independent routes for forcing the Majorana coupling `y_R` from the
J-self-conjugate `(1,1)_0` locus all returned NO or DEGENERATE under
audit-discipline Lean formalization. Each is a real branch with
machine-checked theorems; together they consolidate the
**transcendent-IC framing** for `y_R` as the v0.9.1 standing claim.

| Route | Module | Verdict |
|-------|--------|---------|
| Atiyah-Singer | `IndexJSelfConj/` | NO — chiral index `= 0` for every ν |
| ζ_F-regularization | `ZetaFNuR/` | DEGENERATE — `ζ_F(0; ν_R) = mult`, not 8 |
| Self-Model Deficit (J-fixed) | `SelfModelJFixed/` | NO — closure holds for any `y_R > 0` |
| η-invariant + spectral flow | `EtaJSelfConj/` | DEGENERATE — `η ≡ 0`, net `sf ≡ 0`, APS index 0 |
| Axiom 3 readings A/B/C/D/E | `FaithfulnessForcesYR/` | NO across all five |

Adjacent honest verdicts from this session:

- **MajoranaBlock** — discriminator selects Hypothesis B
  (`mult = 6` under standard NCG Connes-Marcolli §17.5).
- **SAGFJointUniqueness** — verdict **H3**: 1-parameter family in `m_1`;
  closure under spectral-gap-maximization NOT claimed in this branch,
  per the homeostatic-SGM reframe.
- **CorrespondencePrinciple** — verdict **CO-MONOTONE**: across the v0.9
  acceptance window `M_R ∈ [3·10¹⁴, 1.5·10¹⁵] GeV`, the IR-dominant
  Hessian eigenvalue and `λ_1` are strictly co-monotone (mpmath dps=50).
- **EtaB** — Formula A (`λ^14`) bracketed `7.9·10⁻¹⁰ < η_B < 8.1·10⁻¹⁰`
  vs. Formula B (`J²/2`); framework verdict recorded.
- **CompositionUniqueness** (Path A) — among the three named convolution
  candidates, only additive satisfies the three-condition predicate;
  trace law forced **unconditionally** (zero new axioms); narrow
  uniqueness via Mesland-Rennie 2013 / Rosenberg-Schochet 1987 /
  Kassel 1986 is **conditional** on the cited Kasparov-product axioms.

---

## Status at a Glance

Per-module counts after the v0.9.1 release pass (2026-05-10):

| Module | Files | Sorries | Named axioms | Role |
|--------|:-----:|:-------:|:------------:|------|
| Axioms | 4 | 0 | 0 | `L ≥ 0`, `ker L = const`, spectral determination |
| Algebra | 6 | 3 | 2 | CayleyDickson, Hurwitz, SpectralArithmetic, Circulant |
| Analysis | 19 | 6 | 2 | HeatSemigroup, BakryEmery, CheegerColding, Cheeger upper/lower |
| QFT | 30 | 4 | 1 | Lattice gap, OS, WickRotation, ClayStatement |
| Predictions | 9 | 1 | 0 | α_s, Cabibbo, T_c/v, θ_13, δ_CP, Koide |
| Triad | 2 | 0 | 0 | Golden ratio, self-referential triad |
| GR | 3 | 0 | 0 | Placeholders (True := trivial) |
| SelfRef | 5 | 0 | 4 | Gödel trace, Baker form |
| Thermo | 1 | 0 | 1 | Four laws (1 axiom: second law) |
| Cosmology | 7 | 0 | 0 | Friedmann from σ_tr, CMB, e-fold multiplicity |
| Conjectures | 1 | 0 | 2 | Hodge scaffold (Lefschetz) |
| **YukawaHierarchy** | **16** | **0** | **0** | SO(10) instanton scaffold, BPST, anomaly cancel |
| **OP3** | **3** | **0** | **0** | κ₂ / f₄ honest predicate-hypothesis closure |
| **CompositionUniqueness** | **8** | **0** | **5** | Path A: 3-condition forces trace law, narrow uniqueness |
| **MajoranaSelfRef** | **4** | **0** | **1** | ν_R isMajorana; unique J-self-conj in 16 |
| **MajoranaBlock** | **4** | **0** | **6** | Discriminator: Hypothesis B (mult=6) under NCG |
| **IndexJSelfConj** | **3** | **0** | **1** | AS index of J-self-conj sub-block = 0, not 8 |
| **EtaJSelfConj** | **4** | **0** | **0** | η ≡ 0; APS index ≠ 8 |
| **EtaB** | **3** | **0** | **5** | Formula A vs Formula B; bracket on η_B |
| **Eta** | **3** | **0** | **1** | Structural η-invariant; integer counts (12, 144, 168, 768) |
| **ZetaFNuR** | **4** | **0** | **2** | J-restricted ζ at s=0 = multiplicity, not 8 |
| **SelfModelDeficit** | **5** | **0** | **10** | Sector decomposition (288 = 384 − 96) |
| **SelfModelDeficitRigorous** | **6** | **0** | **1** | Rigorous Prop 23.10: predicate-hypothesis form |
| **SelfModelJFixed** | **4** | **0** | **4** | J-fixed locus: NO under standard NCG |
| **FaithfulnessForcesYR** | **6** | **0** | **0** | Axiom 3 readings A/B/C/D/E all return NO |
| **SAGFJointUniqueness** | **4** | **0** | **3** | H3: 1-parameter family in m_1 |
| **CorrespondencePrinciple** | **2** | **0** | **1** | Co-monotone over the v0.9 window |
| **SeeleyDeWitt** | **3** | **0** | **2** | R² sign-triple independence + cutoff-conditional normalization |
| **Total** | **169** | **~15** | **54** | |

---

## Yang-Mills Mass Gap Chain

The core argument, with honest status for each step:

```
TIER 1 (proved in Lean, 0 sorry):
  Axioms 1-2 (RelationalStructure, Laplacian)
    -> L >= 0, ker L = constants, spectral gap lambda_1 > 0
    -> Heat semigroup: PSD, contraction, correlator decay
    -> Bakry-Emery: CD(kappa, inf) -> discrete Lichnerowicz
    -> Cheeger-Colding: antitone + bounded -> converges, gap to limit

TIER 2 (conditional on named, unformalized standard results):
  CompactSimpleGroup carries Lichnerowicz gap as DATA
    -> O'Neill formula Ric(A/G) >= N/4: CITED, not formalized
    -> Lattice eigenvalue antitone property: HYPOTHESIZED
    -> Continuum gap >= N/4: PROVED given the above
    -> OS2/OS3 in continuum: PROVED (OS4 has 1 sorry)

TIER 3 (scaffolding):
  Wightman axioms: bare Prop fields
  Wightman distributions: sorry (OS reconstruction cited)
  clay_yang_mills: GOAL THEOREM (sorry on wightman_n)
```

Key statements:

```lean
-- Tier 1: lattice gap (tautological — extracts user-supplied positive data)
theorem yang_mills_lattice_gap_general (G : CompactSimpleGroup) :
    ∃ (m : ℝ), 0 < m

-- Tier 2: continuum gap (conditional on antitone hypothesis)
theorem assembly_clay_v3 (N : ℕ) (hN : 2 ≤ N)
    (spectral_data : …) (h_antitone : …) :
    ∃ (m : ℝ), 0 < m ∧ (N : ℝ) / 4 ≤ m ^ 2

-- Tier 3: Clay goal (sorry on Wightman distributions)
theorem clay_yang_mills (G : CompactSimpleGroup) :
    ∃ (qft : WightmanQFT) (D : ℝ),
      SatisfiesWightmanAxioms qft ∧ HasMassGap qft D ∧ IsNonTrivial qft
```

---

## What This Formalization Does NOT Prove

Explicit gaps:

1. **Lichnerowicz gap values** are asserted as data on
   `CompactSimpleGroup`, not derived from the Ricci curvature of SU(N)
   with the bi-invariant metric.
2. **The O'Neill formula** `Ric(A/G) ≥ N/4` is cited in comments but not
   formalized.
3. **The Wightman axioms** W1, W2, W4, W5 are bare `Prop` fields; the
   predicates `SatisfiesW1` … `SatisfiesW5` in `ClayStatement.lean`
   reduce to checking `0 < first_excited` (plus trivial conditions),
   not the actual physical content of each axiom.
4. **The eigenvalue antitone property** for lattice refinements
   (needed for Cheeger-Colding convergence to the continuum) is
   hypothesized, not proved.
5. **OS reconstruction** (Euclidean correlators → Wightman
   distributions) is cited as a theorem of Osterwalder-Schrader
   (1973/1975) but not formalized; the `wightman_n` field is `sorry`'d.
6. **The Composition theorem** (former Axiom 4) has narrow Path-A
   uniqueness in `CompositionUniqueness/` but broader uniqueness across
   *all* binary spectral operations remains stated as an open
   hypothesis (`BroaderUniquenessOpen.lean`), not a theorem. v0.9 line
   16783's hand-wavy admission is closed only along Path A.
7. **`y_R` is not derived** from any J-self-conjugate route tested in
   this repository (see "Honest negatives" above). The v0.9.1
   manuscript carries it as a transcendent initial condition.

---

## Redemption History

An adversarial audit on 2026-05-09/10 caught seven deceptive branches.
Each was rewritten under predicate-hypothesis discipline; the resulting
branches are now merged to `main`.

| Branch | Original deception | Redemption |
|--------|--------------------|-----------|
| `zetaF-prime-zero` | Axiomatized constants engineered to sum to 8 | Superseded by `self-model-deficit-rigorous` (predicate form) |
| `Lambda1-refinement` | `kappa2_target := 2·log(Λ_c²/Λ_obs)` made the SCSE match a definitional identity | Predicate-hypothesis form; `λ_1_at_kstar` now conditional on three Prop predicates matching v0.9 open problems |
| `eta-integers-12-144-168-768` | `rfl` proofs on definitional integers | Structural η-invariant `Σ sgn(λ_k)` over `FiniteSpectralTriple`; integer counts emerge from spectral flow, not unfold |
| `majorana-block-residue` | `standard_NCG_three_generation_sum : 6 = 6` and `rfl`-disguised multiplicity | Predicate-over-spectral-triple formalization; integer 6 emerges via 3-step rewrite chain consuming three named axioms |
| `R2-sign` | Per-DOF normalization smuggled in via `cutoff_rescaling_per_dof` axiom | Split into A (unconditional, sign-triple independence) and B (conditional on the cutoff axiom, explicitly named) |
| `SAGF-joint-uniqueness` | 5 of 8 "constraints" tautological `X = X` | Dropped tautologies; only the 5 substantive constraints remain; verdict H3 |
| `composition-uniqueness` | Axiom-smuggling of the conclusion | Path A: trace law forced **unconditionally**; narrow uniqueness conditional on three cited Kasparov-product axioms |

The seven redemption branches were merged sequentially into
`v0.9.1-merge-staging` then fast-forwarded to `main`.

---

## Building

Requires Lean 4 (v4.29.0-rc6) and Mathlib master.

```bash
lake build
```

Full repo build is 3179 jobs.

---

## References

- Ben-Shalom, A. *Spectral Physics* v0.9.1. Ember Research Lab, 2026.
- Ben-Shalom, A. *Yang-Mills Mass Gap via Spectral Geometry*. 2026.
- Jaffe, A. and Witten, E. *Quantum Yang-Mills Theory*. Clay Mathematics
  Institute, 2000.
- Connes, A. and Marcolli, M. *Noncommutative Geometry, Quantum Fields
  and Motives*. 2008.
- Mesland, B. and Rennie, A. *Nonunital spectral triples and metric
  completeness in unbounded KK-theory*. 2013.
- Rosenberg, J. and Schochet, C. *The Künneth theorem and the universal
  coefficient theorem for Kasparov's generalized K-functor*. 1987.
- Kassel, C. *A Künneth formula for the cyclic cohomology of
  Z/2-graded algebras*. 1986.
- Cheeger, J. and Colding, T.H. *On the structure of spaces with Ricci
  curvature bounded below*. 1997.
- Osterwalder, K. and Schrader, R. *Axioms for Euclidean Green's
  Functions*. 1973.
- Bakry, D. and Eméry, M. *Diffusions hypercontractives*. 1985.
- Baker, A. *Linear forms in the logarithms of algebraic numbers*. 1966.
- Vassilevich, D.V. *Heat kernel expansion: user's manual*. 2003.
- Whitt, B. *Fourth-order gravity as general relativity plus matter*.
  1984.

---

## License

Apache 2.0

## Author

[Ember Research Lab](https://ember-research-lab.github.io/) · [emberresearchlab@gmail.com](mailto:emberresearchlab@gmail.com)
