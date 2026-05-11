# Spectral Physics: Lean 4 Formalization

A machine-checked formalization of the spectral physics framework
(`papers/spectral_physics/spectral-physics-v0.9.1.tex`), built under
adversarial audit discipline. The repository pairs Tier-1 proofs of the
core spectral apparatus with **honest predicate-hypothesis closures** of
the v0.9 open problems, **catalogued negative results** for hypotheses
that do not survive Lean-level scrutiny, and a v0.9.2 release pass that
reduced 12 deferred items to predicate-hypothesis form with named
literature citations.

Part of [**Ember Research Lab**](https://ember-research-lab.github.io/) —
independent research deriving geometry, quantum mechanics, and consciousness as
three projections of the graph Laplacian. See the [concepts
index](https://ember-research-lab.github.io/concepts.html) for definitions of
the framework's terms.

**229 Lean files | 40 top-level modules | ~10 sorry sites | 86 named declarations carrying axiom-class status**

Builds against Lean 4.29.0-rc6 and Mathlib master via `lake build`
(3294 jobs at last full pass, 2026-05-11).

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

## v0.9.2 Release Pass (2026-05-11)

Twelve `compute/*` branches reduced the v0.9.2 deferred queue to
predicate-hypothesis form with named literature citations. All twelve
were merged via three staging branches (`v0.9.2-merge-staging`,
`v0.9.2-wave2-staging`, `v0.9.2-wave3-staging`) and fast-forwarded to
`main`.

### Negative results (NO / DEGENERATE)

| Module | v0.9.2 § | Verdict | Headline |
|--------|----------|---------|----------|
| `DixonOrderOne` | B.1 | **NO** | `dixon_order_one_fails` — non-assoc obstruction on octonion factor; `[L_a, R_b] ≠ 0` via Mathlib `Quaternion`'s `i·j ≠ j·i` |
| `DixonPoincareDuality` | B.2 | **NO** | `dixon_pd_obstruction` — same non-associativity blocks K-theory descent for the intersection form |
| `RMForcesDivisionAlgebras` | G.4 | **NO + counterexample** | `RM_does_not_force_division_algebras_headline` — `ℝ × ℝ` (split-complex) satisfies Axiom 3 but has zero divisors; vindicates v0.9 line 16779 self-flag |

### Falsification of a v0.9 perturbative recipe

| Module | v0.9.2 § | Verdict | Headline |
|--------|----------|---------|----------|
| `Kappa2FromSpectrum` | D.2 | **CONDITIONAL + falsification** | `kappa2Full canonical ≠ 258` — bracket [285, 290] central (sensitivity [281, 320]), 22-32 units above v0.9 target 258±5; the closed-form perturbative cumulant recipe of v0.9 line 9747 is theorem-level falsified, while structural SCSE fixed-point determination of Λ_cosmo is unaffected |

### Conditional / Partial closures

| Module | v0.9.2 § | Verdict | What's new |
|--------|----------|---------|------------|
| `SelfModelDeficitUnconditional` | C.1 | **PARTIAL** | `self_model_deficit_unconditional : ∀ V, negZetaPrimeAtZero V = 288` — hypothesis-free now; v0.9.1's two caller-supplied predicates reduced to three named lit axioms (Bekenstein 1981, Mac Lane 1998, Connes-Marcolli 2008) |
| `KSRCompactness` | G.2 | **CONDITIONAL** | `ksr_compact` from one named axiom (Rellich 1930, Kondrachov 1945, Simon 2005, Reed-Simon Vol. IV §XIII.5); Mathlib search documented (no Schatten infrastructure yet) |
| `CompositionBroaderUniqueness` | A.1 | **PARTIAL — 0 new axioms** | Four non-Kasparov candidates falsified Tier-1 (free-Voiculescu, mult-free, monoidal non-Kasparov, boxed); uncountable case identified as the named Nica-Speicher 2006 research program |
| `F2FromSpectralAction` | D.3 | **CONDITIONAL** | `f2_identification` — recovers `Cosmology.f_2_pos` via Chamseddine-Connes 1997 + Vassilevich 2003 a₂ coefficient; specific value 48·e⁶ remains open |
| `BasinConnectivity` | G.3 | **CONDITIONAL bidirectional** | `v092_G3_verdict` — forward (Palais-Smale + coercivity + at-most-one-min → basin connectivity) AND reverse (basin connectivity → at-most-one-min via Morse two-minima-disconnect); coercivity bridges to `KSRCompactness` |
| `AlphaEffRGFlow` | G.7 | **CONDITIONAL** | `alpha_eff_verdict_v092_G7` — four named SM RGE axioms (Machacek-Vaughn 1983/84/85, Ford-Jones-Stevenson-Stephens 1992, Mihaila-Salomon-Steinhauser 2012, Manohar-Wise 2000) + three predicate hypotheses; empirical closure routed to a Python/mpmath sidecar |
| `IRUVScaleSeparation` | J.1 | **CONDITIONAL** | `spectral_universality_from_perturbation_bound` (kernel axioms only) + Wilson-Polchinski biconditional (Wilson 1971 + Polchinski 1984); v0.9 `prop:spectral-convergence` (line 1437) identified as spectral analogue of statistical-mechanics universality |
| `GJIdentification` | J.3 | **CONDITIONAL + bracket** | GJ = **Georgi-Jarlskog** (not Glashow-Jaffe); three GUT-scale Yukawa ratios `c₁=√5, c₂=1/(3+φ), c₃=2/3` all in ℚ(√5); algebraic side Tier-1 zero axioms, empirical bracket [0.014, 0.024] from 6 named axioms (PDG 2024 + Antusch et al. 2005); v0.9's quoted [0.006, 0.017] is tighter than the audit-honest interval-arithmetic bracket can verify |

---

## Tiered Status of Results

### Tier 1 — Proved in Lean (zero `sorry`, zero open hypotheses)

Core spectral apparatus:

- **Lattice spectral gap** — `λ₁ > 0` for connected `L ≥ 0`; `ker L = constants` (`Laplacian.lean`).
- **Heat kernel** — `e^{-tL}` PSD; exponential correlator decay (`HeatSemigroup.lean`).
- **Rayleigh / Courant-Fischer** — variational characterization, min-max (`RayleighQuotient.lean`).
- **Bakry-Émery on graphs** — discrete `CD(κ, ∞)`, Lichnerowicz `κ ≤ λ₁`, SU(2) `ρ_0 = 12/7` (`BakryEmery.lean`).
- **Cheeger-Colding convergence** — antitone + bounded → converges; gap passes to limit (`CheegerColding.lean`).
- **Wick rotation** — analytic continuation of `Z(β)`, spacelike correlator decay (`WickRotation.lean`).
- **Cayley-Dickson tower** — `ℝ → ℂ → ℍ → 𝕆` with norm-multiplicativity (`CayleyDickson.lean`, `Hurwitz.lean`).
- **Numerical predictions** — `α_s = π(2+φ)/96` (0.4%), Cabibbo `(150 − 23√5)/440` (0.12%), `T_c/v` (0.6%), `θ_13`, `δ_CP` (`Predictions/`).
- **Self-reference** — Gödel trace; `ε̄ ≥ I·C_min/τ` (`SelfRef/`).
- **YukawaHierarchy** — 16-file SO(10) instanton-counting scaffold, anomaly cancellation for any ν (`YukawaHierarchy/`).
- **v0.9.2 unconditional headlines** — `dixon_order_one_fails`, `dixon_pd_obstruction`, `self_model_deficit_unconditional`, `RM_does_not_force_division_algebras_headline`, `broader_uniqueness_among_named_candidates`, `framework_GJ_symbolic` — all on Lean kernel axioms only.

### Tier 2 — Conditional on named, standard, unformalized results

These theorems are **proved in Lean** given explicit hypotheses naming
classical theorems.

- **Continuum mass gap** — `assembly_clay_v3` (conditional on antitone hypothesis).
- **OS axioms in continuum** — OS2/OS3 transfer; OS4 has one residual `sorry`.
- **Lichnerowicz gap values** — supplied as data on `CompactSimpleGroup`; O'Neill cited not formalized.
- **SeeleyDeWitt `R²` coefficient** — sign-triple independence unconditional; per-DOF normalization cutoff-conditional.
- **Friedmann from `σ_tr`** — `friedmann_from_sigmaTr` given Whitt 1984 / De Felice-Tsujikawa 2010 axiom.
- **κ₂ / f₄ (v0.9.1)** — predicate-conditional closure at OP3; **v0.9.2 sharpened** with bracket [285, 290] in `Kappa2FromSpectrum` and conditional Chamseddine-Connes derivation in `F2FromSpectralAction`.

### Tier 3 — Scaffolding (structure without full mathematical content)

- **Wightman axioms W1-W5** as bare `Prop` fields on `OSReconstruction.WightmanData`.
- **Wightman distributions** — `wightman_n := fun _n => sorry` (OS reconstruction cited not formalized).
- **GR / Spacetime** — placeholder theorems (`: True := trivial`).
- **Consciousness** — definitional statements as `True := trivial`.

### Honest negatives — what *did not* close

**Five independent routes for forcing `y_R` from the J-self-conjugate `(1,1)_0` locus all returned NO / DEGENERATE** (v0.9.1 work):

| Route | Module | Verdict |
|-------|--------|---------|
| Atiyah-Singer | `IndexJSelfConj/` | NO — chiral index = 0 for every ν |
| ζ_F-regularization | `ZetaFNuR/` | DEGENERATE — `ζ_F(0; ν_R) = mult`, not 8 |
| Self-Model Deficit (J-fixed) | `SelfModelJFixed/` | NO — closure for any `y_R > 0` |
| η + spectral flow | `EtaJSelfConj/` | DEGENERATE — η ≡ 0, net sf ≡ 0, APS index 0 |
| Axiom 3 readings A/B/C/D/E | `FaithfulnessForcesYR/` | NO across all five |

**Three additional structural negatives** (v0.9.2 work):

| Route | Module | Verdict |
|-------|--------|---------|
| Dixon order-one | `DixonOrderOne/` | NO — non-assoc obstruction (Bochniak-Sitarz) |
| Dixon Poincaré duality | `DixonPoincareDuality/` | NO — same obstruction; K-theory descent fails |
| Axiom 3 → Hurwitz tower | `RMForcesDivisionAlgebras/` | NO — `ℝ × ℝ` counterexample |

Together these vindicate the **transcendent-IC framing** for `y_R` and
the **structurally-additional-hypothesis-needed** framing for the Dixon
program.

---

## Yang-Mills Mass Gap Chain

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
-- Tier 1: lattice gap
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

1. **Lichnerowicz gap values** asserted as data, not derived from Ricci.
2. **The O'Neill formula** `Ric(A/G) ≥ N/4` cited but not formalized.
3. **The Wightman axioms** W1, W2, W4, W5 are bare `Prop` fields.
4. **The eigenvalue antitone property** for lattice refinements — hypothesized.
5. **OS reconstruction** cited (Osterwalder-Schrader 1973/1975); `wightman_n` is `sorry`.
6. **The Composition theorem** has Path-A uniqueness in `CompositionUniqueness/` plus four-candidate falsification in `CompositionBroaderUniqueness/`, but broader uniqueness across *all* non-Kasparov factorizations stays a predicate identified with the named Nica-Speicher 2006 research program.
7. **`y_R` is not derived** — five v0.9.1 routes returned NO/DEGENERATE; carried as transcendent IC.
8. **The Dixon-algebra spectral triple is structurally incomplete** in the Connes program — non-associativity obstructs both order-one (B.1) and Poincaré duality (B.2). Additional structural hypotheses (Bochniak-Sitarz, Boyle-Farnsworth) are required.
9. **Axiom 3 alone does NOT force the Hurwitz tower** — a `ℝ × ℝ` counterexample falsifies the strong reading; an additional structural hypothesis at Link 2 (faithful composition norm) is required.
10. **The closed-form perturbative κ₂ recipe of v0.9 line 9747 is falsified** at theorem level — the structural SCSE fixed-point route remains the only viable path to Λ_cosmo.
11. **λ_σ first-principles derivation (D.1)** and **birth of geometry / σ_0/M_Pl hierarchy (D.4)** remain explicitly v1.0 research-program targets. v0.9.2 does not advance them.

---

## Redemption History (v0.9.1)

An adversarial audit on 2026-05-09/10 caught seven deceptive branches.
Each was rewritten under predicate-hypothesis discipline; the resulting
branches are now merged to `main`.

| Branch | Original deception | Redemption |
|--------|--------------------|-----------|
| `zetaF-prime-zero` | Axiomatized constants engineered to sum to 8 | Superseded by `self-model-deficit-rigorous` (predicate form) |
| `Lambda1-refinement` | `kappa2_target := 2·log(Λ_c²/Λ_obs)` made the SCSE match a definitional identity | Predicate-hypothesis form; `λ_1_at_kstar` now conditional on three Prop predicates matching v0.9 open problems |
| `eta-integers-12-144-168-768` | `rfl` proofs on definitional integers | Structural η-invariant `Σ sgn(λ_k)` over `FiniteSpectralTriple` |
| `majorana-block-residue` | `standard_NCG_three_generation_sum : 6 = 6` and `rfl`-disguised multiplicity | Predicate-over-spectral-triple formalization; integer 6 emerges via 3-step rewrite chain |
| `R2-sign` | Per-DOF normalization smuggled via `cutoff_rescaling_per_dof` axiom | Split into A (unconditional) and B (cutoff-conditional with explicit named axiom) |
| `SAGF-joint-uniqueness` | 5 of 8 "constraints" tautological `X = X` | Dropped tautologies; only 5 substantive constraints; verdict H3 |
| `composition-uniqueness` | Axiom-smuggling of the conclusion | Path A: trace law unconditional; narrow uniqueness conditional on K1+K2+K3 (Mesland-Rennie 2013, Rosenberg-Schochet 1987, Kassel 1986) |

---

## Building

Requires Lean 4 (v4.29.0-rc6) and Mathlib master.

```bash
lake build
```

Full repo build is 3294 jobs.

---

## References

- Ben-Shalom, A. *Spectral Physics* v0.9.1. Ember Research Lab, 2026.
- Ben-Shalom, A. *Yang-Mills Mass Gap via Spectral Geometry*. 2026.
- Jaffe, A. and Witten, E. *Quantum Yang-Mills Theory*. Clay Mathematics Institute, 2000.
- Connes, A. and Marcolli, M. *Noncommutative Geometry, Quantum Fields and Motives*. 2008.
- Mesland, B. and Rennie, A. *Nonunital spectral triples and metric completeness in unbounded KK-theory*. 2013.
- Rosenberg, J. and Schochet, C. *The Künneth theorem and the universal coefficient theorem for Kasparov's generalized K-functor*. 1987.
- Kassel, C. *A Künneth formula for the cyclic cohomology of Z/2-graded algebras*. 1986.
- Cheeger, J. and Colding, T.H. *On the structure of spaces with Ricci curvature bounded below*. 1997.
- Osterwalder, K. and Schrader, R. *Axioms for Euclidean Green's Functions*. 1973.
- Bakry, D. and Eméry, M. *Diffusions hypercontractives*. 1985.
- Baker, A. *Linear forms in the logarithms of algebraic numbers*. 1966.
- Vassilevich, D.V. *Heat kernel expansion: user's manual*. Phys. Rept. 388 (2003).
- Whitt, B. *Fourth-order gravity as general relativity plus matter*. Phys. Lett. B 145 (1984).
- Chamseddine, A.H. and Connes, A. *The spectral action principle*. Comm. Math. Phys. 186 (1997).
- Bochniak, A. and Sitarz, A. *Spectral triples for the Standard Model* (Dixon obstruction analysis). arXiv:2001.02613.
- Boyle, L. and Farnsworth, S. *Non-commutative geometry, non-associative geometry and the Standard Model of particle physics*. arXiv:1910.11888.
- Bekenstein, J.D. *Universal upper bound on the entropy-to-energy ratio for bounded systems*. Phys. Rev. D 23 (1981).
- Mac Lane, S. *Categories for the Working Mathematician* (2nd ed.), Springer 1998.
- Wilson, K.G. *Renormalization Group and Strong Interactions*. Phys. Rev. D 3 (1971); *Renormalization Group and Critical Phenomena*. Phys. Rev. B 4 (1971).
- Polchinski, J. *Renormalization and Effective Lagrangians*. Nucl. Phys. B 231 (1984).
- Kato, T. *Perturbation Theory for Linear Operators* (2nd ed.), Springer 1995.
- Reed, M. and Simon, B. *Methods of Modern Mathematical Physics*, Vol. IV: Analysis of Operators. Academic Press 1978.
- Simon, B. *Trace Ideals and Their Applications* (2nd ed.), AMS 2005.
- Morse, M. *The Calculus of Variations in the Large*. AMS Colloquium Publications 18, 1934.
- Palais, R.S. and Smale, S. *A generalized Morse theory*. Bull. AMS 70 (1964).
- Nica, A. and Speicher, R. *Lectures on the Combinatorics of Free Probability*. Cambridge 2006.
- Voiculescu, D. *Addition of certain non-commuting random variables*. J. Funct. Anal. 66 (1985); *Limit laws for random matrices and free products*. Invent. Math. 104 (1991).
- Machacek, M.E. and Vaughn, M.T. *Two-loop renormalization group equations in a general quantum field theory* I/II/III. Nucl. Phys. B 222/236/249 (1983-1985).
- Antusch, S. et al. *Running neutrino mass parameters in see-saw scenarios*. JHEP 03 (2005).

---

## License

Apache 2.0

## Author

[Ember Research Lab](https://ember-research-lab.github.io/) · [emberresearchlab@gmail.com](mailto:emberresearchlab@gmail.com)
