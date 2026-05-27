# Lean–Manuscript Alignment Gap Register

**Date:** 2026-05-27. **Mode:** read-and-classify only (no fixes, no formalization, no edits).
**Repo:** `Spectral-Physics-Lean` @ `main` (build green, 3324 jobs). **Manuscript:** `spectral-physics-latest.tex` (v1.0).
**Sources:** five independent chain audits (foundations & algebra, particle physics, QFT/Yang–Mills,
self-reference, gravity) + the cosmology rows from `results/CHAIN-RIGOR-LEDGER.md`. Every `#print axioms`
result is from read-only `lake env lean` on the built oleans (`sorryAx` in the trace = transitively depends
on a `sorry`).

## How to read this

Each gap is **Category A** (formalization lag — the manuscript genuinely derives it, Lean is *silent*;
the alignment program advances Lean) or **Category B** (audit finding — Lean *formalized/checked* the claim
and exposes a defect; the alignment program revises the **manuscript** down — Lean must NOT be "advanced" to
match, since matching re-introduces the defect) or **UNDETERMINED**.

**Cross-cutting observation.** The repo is unusually *self-honest*: nearly every B-item is already pre-flagged
in a docstring, `STATUS.md`, the README, or `CHAIN-RIGOR-LEDGER.md`. The B-list below is therefore mostly
**places where the manuscript's tier label or "closed/derived" framing exceeds what the Lean actually
establishes**, not hidden deception. The single largest clean Category-A region is QFT/Yang–Mills, where the
manuscript is scrupulously honest (claims only a compact-base spectral gap; explicitly cites the ℝ⁴ continuum
and OS/Wightman reconstruction as unaddressed open problems).

---

## 1. Foundations & Algebra

| Manuscript claim (ch/line) | Lean (file:theorem) | Cat | Evidence | Notes |
|---|---|---|---|---|
| Koide `K=2/3` "exact algebraic identity from circulant structure", **Tier 1** (`thm:koide` ~11804); status §12047 says "`norm_num` discharges the symbolic expansion" | `Predictions/KoideFormula.lean:circulant_implies_koide` (:48) | **B** | `#print axioms` → `sorryAx`; body `sorry` (:59) | **Most serious finding.** Statement is also *false as written* (no `ε²=2` constraint; equal masses give `K=1/3`). Manuscript Remark 11872 concedes `ε=√2` is a **fit**. The "`norm_num` discharges it" status claim is false. |
| Same Koide claim, also cites `CirculantMatrix.lean` (~12057) | `Algebra/CirculantMatrix.lean:koide_from_circulant` (:118) | **B** | `sorryAx`; `sorry` at :120; supporting `circulant_sqrt_sum_identity` `sorry` at :142 | The √-sum identity (:142) is plausibly A in isolation, but the headline Tier-1 result it feeds is unproved. |
| Koide circulant Z₃-forcing structure | `Predictions/KoideFormula.lean:triad_circulant_structure` (:145) | **B** | `True := trivial`, zero axioms | Prop-shell standing for the structural claim. |
| Koide numerical agreement w/ PDG lepton masses | `Predictions/KoideFormula.lean:koide_approx` (:75) | **A (clean)** | kernel-only axioms; real √-interval bracket `|K−2/3|<0.001` | Genuine; only the *headline* circulant⇒2/3 is unproved. |
| Bakry-Émery discrete Lichnerowicz `κ≤λ₁`, Tier 1 | `Analysis/BakryEmery.lean:lichnerowicz` | **A (clean)** | kernel-only | Real conditional theorem. |
| SU(2) Bakry-Émery rate `ρ₀=12/7`, Tier 1 | `Analysis/BakryEmery.lean:bakry_emery_su2_bound` | **B** | statement is `12/7 = 2·2·3/(2·2+3) := by norm_num` | Tautology; the physical `κ=2, gap=3` content is docstring-only. |
| Cheeger-Colding spectral convergence | `Analysis/CheegerColding.lean:cheeger_colding` | **A (clean, honest T2)** | kernel-only; deep content baked into `eigenvalue_antitone` struct field | Manuscript tags **Tier 2** (Sturm/Lott-Villani) — consistent. |
| Discrete Cheeger `δ₁≥h²/2dₘₐₓ`, "Cheeger 1970, Standard" (`thm:cheeger-bound` ~2165) | `Analysis/DiscreteCheeger.lean:cheeger_lower_bound` (:224) | **A** | `sorryAx`; co-area / median trick not in Mathlib | Manuscript cites a *standard external* theorem; not cited to this file. Formalization lag. |
| Cheeger inequality (abstract) | `Analysis/CheegerInequality.lean:cheeger_lower/upper` | **A (disclosed axiom)** | postulated `axiom` (README counts them) | Citing Cheeger 1970; disclosed. |
| Hurwitz tower dim ≤ 8 / power-of-2, Tier 1 (`thm:hurwitz` ~2836, open-flagged ~963) | `Algebra/Hurwitz.lean:composition_dim_le_eight` | **A (disclosed axiom)** | rests on `axiom composition_algebra_tower_step` | Manuscript ~963 + README explicitly disclose Axiom-3-alone doesn't force the tower (ℝ×ℝ counterexample). Honest. |
| Cayley-Dickson tower ℝ→ℂ→ℍ→𝕆, norm-mult., Tier 1 | `Algebra/CayleyDickson.lean` (mul/star/norm), `Hurwitz.lean:normSq_mul` | **A (clean)** | genuine definitional unfoldings; `not_assoc_of_not_comm`, `cdNorm_sq` real | Algebraic construction substantively clean. |
| Newton/power-sums determine spectrum | `Algebra/SpectralArithmetic.lean:power_sums_determine_spectrum` (:69) | **A** | `sorryAx` (:81); Newton-Girard missing in Mathlib | Not a manuscript headline. Supporting `vandermonde_det_ne_zero` clean. |
| Monograph Prop 1.3 `Z_{M×F}=Z_M·Z_F`; Thm 1.7 resonance sub-linearity; Tr/Tr² identities | `SpectralArithmetic.lean:cpf_product (:133), resonance_sublinear (:153), trace_eq_eigenvalue_sum (:86), trace_sq (:90)` | **B** | `True := trivial` shells; `X = X := rfl` | Cited in docstrings as monograph theorems; carry zero content. |
| Rayleigh / Courant-Fischer **min-max**, "Tier 1, zero sorry" (README ~136, cites `RayleighQuotient.lean`) | `Analysis/RayleighQuotient.lean` (min-max) | **UNDETERMINED → README-only** | **build-orphan** (not imported by root; no olean); source proves only `λ₁ ≤ R(f)`, says "we don't formalize the full min-max" | The **manuscript does not cite min-max / Courant-Fischer at all** → not a manuscript-alignment gap; it is a README overclaim of a Lean-internal incompleteness. `Analysis/CourantFischer.lean:courant_fischer` (in build) has the equality `sorry`'d (`courant_fischer_le` clean, `_ge`/`weyl_perturbation` `sorryAx`) — also not manuscript-cited. |

**Counts:** A = 6 · B = 8 · UNDETERMINED = 1.

---

## 2. Particle Physics

| Manuscript claim (ch/line) | Lean (file:theorem) | Cat | Evidence | Notes |
|---|---|---|---|---|
| Cabibbo `λ=(150−23√5)/440`, Tier 2 | `Predictions/CabibboAngle.lean:cabibbo_closed_form, _agreement` | **A (clean)** | sorry-free; derived from τ; 0.12% | Framework's strongest genuine prediction. |
| θ₁₃ ≈ λ/√2, Tier 2 (`prop:theta13` ~11906) | `Predictions/NeutrinoAngle.lean:neutrinoAngle_approx` | **A (clean)** | sorry-free; 6% | λ framework-derived; 1/√2 structural (matches Tier-2). |
| η_B ≈ λ¹⁴ ≈ 8.0×10⁻¹⁰, Tier 5 (`prop:eta` ~24566) | `EtaB/Formulas.lean:etaB_FormulaA`, `Comparison.lean:etaB_FormulaA_gt_observed` | **A (clean)** | sorry-free; Lean caught & corrected the prior 4.4e-10→8.0e-10 error | Honest pattern-match (Tier 5). |
| η_B `^obs = 6.10×10⁻¹⁰` (Planck) | `EtaB/Comparison.lean:etaB_observed` | **A (clean)** | named axiom, used only on the comparison side | Consistency-check framing correct (η_B^A independent). |
| η_B "framework verdict" `= J²/2 = 4.5×10⁻¹⁰` | `EtaB/Verdict.lean:framework_endorsed_value` | **B (mild, self-flagged)** | depends on `Jarlskog, Jarlskog_value`; built from the **observed PDG** Jarlskog | `Formulas.lean:77` tags J "observational input, NOT framework-derived." Prediction-from-observable; self-flagged. |
| GJ algebraic ratios `c₁=√5, c₂=1/(3+φ), c₃=2/3` (~11036) | `GJIdentification/AlgebraicComputation.lean` (`gj_c1/2/3_algebraic`) | **A (clean / T1)** | symbolic in ℚ(√5), zero axioms | Manuscript flags the *identification* as numerical-not-proven (`rem:gj-epistemic`). |
| GJ empirical ratios `2.200/0.215/0.663` (`eq:gj-coefficients`) | `GJIdentification/EmpiricalBracket.lean` (6 axioms) | **B (mild, honest Tier-2)** | 3 opaque `axiom : ℝ` + 3 bracket axioms (PDG/2-loop-RG) | Axiomatized **observation** = the comparison target, not dressed as a prediction. Correctly Tier-2. |
| GJ "framework predicts ℚ(√5)" | `AlgebraicComputation.lean:framework_predicts_GJ_in_Q_sqrt5 / framework_GJ_symbolic` | **B (mild, self-flagged)** | `⟨rfl,rfl,rfl⟩` — a `:=True`-equivalent shell | Docstring admits it is the *symbolic* (tautological) identification; real open content is the bracket. |
| Self-Model Deficit see-saw closure `S_charged+S_νL+S_νR=288` (`thm:self-model-deficit` 8435; `open:self-model-deficit-proof` 1059) | `SelfModelDeficit/SeeSawCancel.lean:seeSaw_closure`; `Yukawas.lean` | **B** (+A on manuscript side) | `norm_num` on hand-entered decimals incl. `S_νR=−174.01` (the residual chosen so the sum hits the target 288); `y:VisFermion→ℝ` opaque axiom; M_R-independence is a Tier-2 axiom | "Spectral computation" collapses to a constant fixed by the target. Manuscript flags *exactness* OPEN (1059) → that part is honest/A; the Lean "closure" theorem is the B. |
| Σmν NH-floor bracket from measured Δm² (`pred:neutrino-mass`) | `Predictions/NeutrinoMass.lean:sigmaMnu_floor, sigma_m_nu_in_window` | **A (clean)** | genuine √-analysis; NH kinematic floor | The genuinely-independent route (Route 1). |
| Σmν "two **independent** routes" (~167) | `Cosmology/NeutrinoMassPrediction.lean:two_route_consistency` | **B** | `norm_num` on quoted literals; file's own caveat (33–45) says Route 2 (`ξ_R=3.7090`) is tuned to the CC Baker target | The "two independent routes" label is the **mislabel** (Route 2 = consistency check on CC tuning, not corroboration). |
| `y_c/y_τ = N_c/dim(16)` ratio | `YukawaHierarchy/CharmTauRatio.lean:charmTauRatio` | **A (clean)** | translation-invariant ratio identity | Not a tuned-constant false positive. |
| Hypothesis A: (1,1)₀ block mult-1 | `MajoranaBlock/HypothesisA.lean:hypothesis_A_requires_J_quotient` | **A (clean, conditional)** | honestly conditional; file proves SM triple *violates* it; `y_R_target` is an isolated positivity input | Exemplary honest tagging. |
| y_R as "transcendent IC" / self-ref closure | `MajoranaSelfRef/{SelfReferenceClosure,TriadicPartition,Verdict}.lean` | **A (clean, NEGATIVE)** | `y_R_target=327/1e7` is an empirical comparison anchor; verdict explicitly NEGATIVE / "suggestive not forcing"; `y_R=τ⁸` is a Tier-3 axiom not consumed by any Tier-1 result | `y_R_target` is NOT a closure input — no false positive. |

**Counts:** A = 11 · B = 6 (3 substantive, 3 mild/self-flagged) · UNDETERMINED = 0.

---

## 3. QFT / Yang–Mills

| Manuscript claim (ch/line) | Lean (file:theorem) | Cat | Evidence | Notes |
|---|---|---|---|---|
| YM mass gap, **Tier 1 SU(2) on compact base** (`thm:ym-mass-gap` 15929); continuum on ℝ⁴ "not addressed" (15849); `open:ym-continuum-rigor` 16075 | `QFT/ClayStatement.lean:clay_yang_mills` (:337) | **A** | `sorryAx`; top-level `sorry` on `wightman_n` only; 5 Wightman preds + gap + nontriviality discharged from `CompactSimpleGroup` data | Manuscript explicitly does NOT claim the ℝ⁴ Clay theorem. The sorry contradicts no manuscript claim → formalization lag. |
| Lattice / continuum spectral gap (compact base) | `ClayStatement:assembly_clay_v3`, `YangMillsExistence:yang_mills_lattice_gap_general, ym_mass_gap_general` | **A (clean, but gap-VALUE is data)** | kernel-only; reduce to `∃ m, 0<m` from `CompactSimpleGroup.h_lichnerowicz` (user-supplied positivity) | Cheeger-Colding content genuine; the gap value is assumed data (Tier-2, disclosed by README + manuscript: O'Neill/Lichnerowicz "cited, not formalized"). |
| OS axioms (`thm:os-axioms` 10306 claims **only OS1+OS2** with content) | `QFT/OSAxiomsProved.lean:wightmanFromSpectral` (:182); `os1/os2/os3/os4_proved` | **A** | `wightmanFromSpectral` `sorryAx` (single sorry on `wightman_n`, labeled "OS reconstruction 1973/75, not our result"); OS1–OS4 proved sorry-free above | Manuscript claims match what Lean proves (OS1/OS2). The reconstruction sorry is a cited open problem. |
| (OS type machinery) | `QFT/OSAxiomTypes.lean:spectral_to_os` (:165); `OS2/OS3/OS4 := True` (:97/109/119) | **A** | `sorryAx`; the `:=True` OS shells sit beneath it | Broader Prop-shells than expected, but manuscript claims none of these → A. |
| OS4 continuum | `QFT/ContinuumLimit.lean:os4_continuum` (:168) | **A** | `sorryAx`; supporting Finset-sum lemma, "PROOF GAP"; OS1/2/3 continuum sorry-free | Supporting-lemma lag. |
| Orientation independence (paper Thm 5.8) | `QFT/OrientationIndependence.lean:orientation_independence (:169), poincare_from_orientation_independence (:201)` | **A (but Lean-vacuous)** | clean axioms but conclusions are `∃ rate, 0<rate` and `True`-hyps ⇒ `∃ m, 0<m`; supporting `staircase_error_vanishes_first_term` `sorryAx` | Manuscript claim is paper-level, not asserted Lean-proven; the Lean theorem is decorative. |
| Wightman reconstruction (full) | `QFT/OSReconstruction.lean` bare-Prop W1–W5; `ClayStatement:SatisfiesW3 := True` (:163) | **A (honest Tier-3 scaffolding)** | Prop fields instantiated as `0<gap`; self-flagged "Honesty Note"; README labels Tier-3 | Manuscript states reconstruction unaddressed → A, not B. |
| — (Lean-internal) | `OSAxiomsProved.lean` (name) / `clay_yang_mills` (name) | **UNDETERMINED → repo-hygiene** | naming evokes a settled Clay/OS proof while a `sorry` remains | No manuscript counterpart to falsify. Flag for the Lean repo (rename / `Scaffolding` namespace), NOT the manuscript. |

**Counts:** A = 8 · B = 0 · UNDETERMINED = 1 (Lean-side naming, no manuscript counterpart).
**This chain is a clean Category-A region** — the manuscript is honest about what it does and does not claim.

---

## 4. Gravity & Cosmology

(Cosmology rows condensed from `CHAIN-RIGOR-LEDGER.md`; gravity from the self-reference+gravity audit.)

| Manuscript claim (ch/line) | Lean (file:theorem) | Cat | Evidence | Notes |
|---|---|---|---|---|
| CC magnitude `Λ = λ₁`, value matches obs | `OP3/CosmologicalConstantMatch.lean`; `SelfModelDeficit/Kappa2.lean` | **B** | `κ₂=529.42` **is** `2·ln(Λ_c²/Λ_obs)` (Kappa2 docstring ~49); chain runs `Λ_obs→κ₂`; `f4_overshoots_cc_target` proves the honest Edgeworth `f₄≈2.11e-111` overshoots `Λ_obs/M_Pl²` by ~10 orders | The CC *magnitude* is reverse-engineered, not predicted. OP3 match is an honest biconditional + `PredictionMatchesObservation` hypothesis (firewall intact). |
| A_s ≈ 2.1×10⁻⁹ closure (`5³·2²` structural factor; v0.9.1 had "2.4%") | `InflationAsClosure/CombinedClosure.lean:inflation_As_closure`; `axiom A_s_observed_planck2018` | **B** | the theorem's conclusion bounds only the **structural factor** (500 vs 510); the A_s-transfer hyps are discarded (`let _ := …`); `A_s_observed_planck2018` is an axiomatized observation | Docstring already rescoped (2026-05) to say it does NOT formally bound A_s. Over-named; manuscript should not present it as an A_s closure. |
| Cosmic energy budget `Ω_DM=τ, Ω_b=τ²/φ, Ω_Λ=1−τ−τ²/φ`, **Tier 3** (`prop:omega-budget` 23627) | `Predictions/CosmicEnergy.lean` | **A (clean, honest T3)** | sum-rule exact; T1 brackets ~1–3σ of measured; Ω_Λ flagged closure-residual | Lean matches the manuscript's own Tier-3 + residual framing. Honest. |
| Dark-energy `w(z)` evolving `w₀>−1, w_a<0`, **Tier 4** (`sec:self-stiffening-wz` 23727) | `Cosmology/DarkEnergyEoS.lean` | **A (clean, honest T4)** | `IsSelfStiffening` is a load-bearing hypothesis (verified non-vacuous) + proved kinematic consequences | Honestly Tier-4 (values need full SAGF). Matches manuscript. |
| Hubble tension partial, **Tier 3** (`thm:hubble-tension` 24589) | `Cosmology/HubbleTension.lean` | **A (clean, honest T3)** | `α=g·r_s/L_H≈0.017`, ~20%, 5σ→4σ; `partial_mechanism_only` (<1/3) | Honest "NOT a resolution"; g=0.5 a fit. Matches manuscript. |
| Friedmann from `σ_tr>0` (~5468) | `Cosmology/FriedmannEquation.lean:friedmann_from_sigmaTr` | **B** | conditioned on a `ConformalFrameTransform` class whose Whitt-1984 content (frame equivalence, metric variation) is a **docstring, not an axiom**; the instance auto-discharges; kernel-only | The proven ODE algebra is genuine (A); the *physics link* is carried by a trivially-instantiable class. README "given Whitt 1984 axiom" overstates what is encoded. |
| σ₀/M_Pl `=12/√(32π)`, **Tier 1 algebraic** (`thm:sigma-MPl` 14732) | — (no Lean theorem) | **A (gap)** | Mathlib has the pieces; the Tier-1 closed-form algebra is simply not formalized | Genuine formalization lag (README flags D.4 as a research target). |
| σ₀/M_Pl via Akrami–Majid braided Hodge period ("closes 11% A_s gap") | `SigmaMPlHodgePeriod/MainConditional.lean:sigma_MPl_hodge_period_AM_explicit` | **B** | `chern_pairing_log_ratio := 0`, `log_sigma_0_over_M_Pl_inv := id`, hyps `PUnit`/`∃_:PUnit,True`; proof = `rw`; **kernel-only (zero AM/Kassel content)** | Tautology shell that "closes" a claim the **manuscript itself labels superseded/Historical/Tier-4** (`thm:As-closure` 14864). Self-flagged in docstrings. |
| `KassellKunnethTor`/`OctonionBraidedHC` literature axioms | `KassellKunnethTor.lean:HasRankOneTorMinusOneBidegree11 := True (:107)`; `OctonionBraidedHC.lean := PUnit / True / decide` | **B (vacuous shells, but remediated+flagged)** | demoted to `def := PUnit` / `theorem := trivial` with audit docstrings; `HasRankOne…` is UNUSED | The prior "FRAGILE opaque-≃ axioms" concern is **outdated** — the 2026-05 pass already converted them to honestly-labeled vacuous shells. |
| SeeleyDeWitt `R²` coefficient (Thm A sign-independence; Thm B per-DOF 1/288) | `SeeleyDeWitt/R2Coefficient.lean`, `SpectralActionR2.lean` | **A (clean / honestly conditional)** | Thm A unconditional (`rfl` + cited CCM axiom); Thm B explicitly conditioned on `CutoffNormalization`, docstring "conventional identity, not a derivation" | README accurate. Not conditional-dressed-as-unconditional. |

**Counts (gravity+cosmology):** A = 6 · B = 5 · UNDETERMINED = 0. (CC magnitude / κ₂ overlaps §5.)

---

## 5. Self-Reference

| Manuscript claim (ch/line) | Lean (file:theorem) | Cat | Evidence | Notes |
|---|---|---|---|---|
| Gödel-trace accuracy bound `ε̄ ≥ I·C_min/τ` (Thm 9.5/11.1) | `SelfRef/GodelTrace.lean:accuracy_integration_tradeoff, godel_trace` | **A (clean, Tier 1)** | genuine Cauchy-Schwarz / AM-HM; kernel-only | Real content. |
| **Open Problem 21** / κ₂ inputs: "lift Lean `def`s to `theorem`s" (one formalization gap) | `SelfModelDeficit/Kappa2.lean` defs `kappa2_vis, kappa2_hid, mu_vis, mu_hid` | **B (mislabel) — SPLIT** | `kappa2_vis` + means = **A** (computable from Baker mass *ratios*); `kappa2_hid = 2(ξ_R−32)²/3` at the bisection-root `ξ_R=3.7090` fixed by the CC target = **B** (one knob fixed by an observable) | The manuscript treats all of OP21 as one A-type gap — the A/B split is real and the single-gap framing **hides the circular input**. Record the mislabel. |
| `f₄ = f₂·exp(−κ₂/2)` standing prediction | `F4Coefficient.lean:f_4_verdict, f4_overshoots_cc_target` | **A (clean)** | kernel-only; Edgeworth `f₄≈2.11e-111` genuine; overshoots CC by ~10 orders | Lean clean + honest (refuses to close CC). Defect is upstream (κ₂ tuning), not here. |
| `−ζ̃'_vis(0)=288` ⇒ Baker form `288 = C₀+214lnφ+110ln5+ν` (Thm 30.1) | `SelfRef/BakerForm.lean:dim_288_baker_form` | **B** | `∃ C0 ν, …` proved by `ring` choosing `C0` to absorb everything; Baker form not shown to *produce* 288. `critical_point_isolated`, `effective_separation` vacuous (`η:=|Δ|`, Baker bound never invoked) | `baker_form_nonzero` legitimately uses a real cited Baker axiom (A). The existence claims are vacuous shells (B). |
| Consciousness chapters (Tier 3/4/5 narrative; "no Lean formalization exists" ~613) | `SelfRef/Consciousness.lean` (`: True := trivial`; `X=X` rfl) | **A (honest Tier-3)** | placeholders match the manuscript's explicit "no Lean formalization" | Would be B only if presented as a result; it is not. |
| Self-Model Deficit "PARTIAL unconditional" `∀V, negZetaPrimeAtZero V = 288`, reduced to "**three named literature axioms** (Bekenstein 1981, Mac Lane 1998, Connes–Marcolli 2008)" (`UnconditionalGoal.lean:114`, README PARTIAL) | `SelfModelDeficitUnconditional/UnconditionalGoal.lean:self_model_deficit_unconditional` | **B — SEVERE (UNSOUND)** | The two Lean axioms are **logically inconsistent**: `BekensteinInformationBound (S)(c:ℝ) : c ≤ S.dimHid` and `NaturalityCoherence (S)(c:ℝ) : S.dimHid ≤ c` are each universally quantified over `c`, hence each is FALSE (`c=dimHid±1`). Verified: `theorem bek_inconsistent : False := by have h := BekensteinInformationBound spectralPhysicsSectoredAlgebra (dimHid+1); linarith` compiles with `#print axioms = [propext, Classical.choice, Quot.sound, BekensteinInformationBound]` — **no `sorryAx`**. So `False` (and `0=1`) is derivable; the `=288` headline is `le_antisymm` between two inconsistent bounds. | **Most severe finding in the audit.** Not vacuous and not `sorry`'d — it *looks* proven (clean `#print axioms` showing "named axioms"), but is logically unsound. The Lean axioms do NOT faithfully encode Bekenstein/Mac Lane (which are not `∀c, c≤dimHid`); the intended statement fixes `c = negZetaPrimeAtZero V`, not all reals. The over-quantification is the bug. NEW class missed by `3f66049` (which caught the `:=True`-predicate→`0=1` route; these are directly-false inequality axioms, invisible to `check_axioms.sh`'s `∃_,True` patterns). **Blast radius:** the axioms are in the root build; any theorem whose `#print axioms` includes either is unsound. FIX (do NOT apply in this audit): restrict `c` to the specific information content. |

**Counts:** A = 3 (+f₄) · B = 4 (one **SEVERE/unsound**) · UNDETERMINED = 0.

---

## Summary

### Per-chain counts

| Chain | A | B | UNDETERMINED |
|---|---:|---:|---:|
| Foundations & algebra | 6 | 8 | 1 (RayleighQuotient — README-only, not a manuscript gap) |
| Particle physics | 11 | 6 (3 substantive + 3 mild) | 0 |
| QFT / Yang–Mills | 8 | 0 | 1 (Lean naming — repo-hygiene, no manuscript counterpart) |
| Gravity & cosmology | 6 | 5 | 0 |
| Self-reference | 3 (+f₄) | 4 (**1 SEVERE / unsound**) | 0 |

Cross-chain duplicates: **κ₂/CC magnitude** appears in both Gravity&Cosmology and Self-reference (one defect);
**Σmν Route-2** appears in both Particle and Cosmology (one defect). Deduplicated, the substantive B-list is below.

### Manuscript-revision queue (HEADLINE Category-B — the deliverable's payload)

These are the headline claims where the manuscript's framing exceeds what Lean establishes. **Do not "advance"
the Lean to match any of them** — matching re-introduces the defect.

0. **[SEVEREST — UNSOUND] Self-Model Deficit "PARTIAL unconditional" `−ζ̃'_vis(0)=288`** — the two Lean axioms
   `BekensteinInformationBound`/`NaturalityCoherence` (`∀c, c≤dimHid` / `∀c, dimHid≤c`) are **logically
   inconsistent** (verified: `False` derives from each, no `sorryAx`; `#print axioms bek_inconsistent =
   [propext, Classical.choice, Quot.sound, BekensteinInformationBound]`). The `=288` headline is `le_antisymm`
   between two inconsistent bounds — it *looks* proven (clean `#print axioms` showing only "named axioms") but
   is unsound, and the axioms sit in the **root build**. The manuscript's "reduced to three named literature
   axioms" framing is illusory: the Lean axioms don't encode Bekenstein/Mac Lane (they over-quantify over `c`).
   More insidious than every item below — no `sorry`, no `:=True`, so it passes a naive axiom audit. **Fix:
   restrict `c` to the specific information content; until then `=288` is not established.**

1. **Koide `K=2/3` "Tier-1 exact from circulant"** — `circulant_implies_koide` + `koide_from_circulant` are
   both `sorry` (sorryAx); `circulant_implies_koide` is *false as written* (no `ε²=2`); manuscript Remark
   11872 concedes `ε=√2` is a fit; the status claim "`norm_num` discharges it" is false. **Highest priority.**
   Revise to: K=2/3 is conditional on the `ε²=2` (Cayley-Dickson) input — Tier 2, and the Lean is unproved.
2. **κ₂ / CC magnitude tuned to `Λ_obs`** — `κ₂_hid`/`ξ_R` solved backward from `2·ln(Λ_c²/Λ_obs)`; the CC
   *magnitude* is not a prediction. **OP21 is mislabeled** as a single A-type formalization gap — split it
   (visible cumulant + means = A; hidden cumulant = B-circular).
3. **σ₀/M_Pl Akrami–Majid Hodge "closure"** — `sigma_MPl_hodge_period_AM_explicit` is a tautology shell
   (kernel-only, zero AM content) closing a claim the manuscript itself marks **superseded**. Separately, the
   manuscript's genuine Tier-1 σ₀/M_Pl = 12/√(32π) algebra is **not in Lean** (an A gap, not this chain).
4. **"288" see-saw closure** — `S_νR=−174.01` back-fit so the decimals sum to the target 288; M_R-independence
   axiomatized. (Manuscript already flags exactness OPEN — keep it OPEN, don't present the arithmetic as a closure.)
5. **Σmν "two independent routes"** — Route 2 (`ξ_R` bisection) is tied to the CC tuning; not independent.
   Revise to: one independent route (functional determinant + NH kinematic floor).
6. **A_s "closure"** — `inflation_As_closure` bounds only the `5³·2²` structural factor, not `|A_s−A_s_obs|`;
   rests on `axiom A_s_observed_planck2018`. Present as a structural-factor result, not an A_s prediction.
7. **`friedmann_from_sigmaTr`** — the Whitt-1984 physics link is a docstring, not an axiom/theorem; the class
   auto-discharges. Either encode the content or drop the "derived" framing.
8. **Tautology / vacuous-marker headline theorems** — SU(2) `ρ₀=12/7` (`12/7=12/7`); `SpectralArithmetic`
   monograph "theorems" (`cpf_product`, `resonance_sublinear`, trace identities — `True`/`X=X`); Baker
   existence claims (`dim_288_baker_form`, `critical_point_isolated`, `effective_separation`). Carry no content.

### Mild / honestly-tagged B (lower priority — self-flagged, not deceptive)
GJ empirical bracket (6 data-side axioms, correctly Tier-2); GJ `framework_predicts_GJ_in_Q_sqrt5` (a
`⟨rfl,rfl,rfl⟩` predicate whose docstring admits it is the symbolic-only identification); η_B `J²/2` built
from the observed Jarlskog (J explicitly tagged observational); `SigmaMPlHodgePeriod` `:=PUnit`/`True` shells
(already demoted + flagged in the 2026-05 audit).

### Clean Category-A confirmed (advance Lean later, or already honest)
Cabibbo λ, θ₁₃, η_B Formula-A (λ¹⁴), Σmν NH-floor, GJ algebraic side, Bakry-Émery Lichnerowicz, Cheeger-Colding
(Tier-2), Cayley-Dickson construction, Gödel trace, f₄ Edgeworth, the cosmic budget / w(z) / Hubble tension
(all honestly Tier-3/4), SeeleyDeWitt R². The **entire QFT/Yang–Mills chain is clean A** — the manuscript is
honest that it claims only a compact-base spectral gap and leaves the ℝ⁴ Clay continuum / OS reconstruction open.

### Lean-side (non-manuscript) hygiene flags
- `OSAxiomsProved.lean` contains a `sorry`; `clay_yang_mills`/`assembly_clay_v3` names evoke a settled Clay
  proof. Rename / move to a `Scaffolding` namespace. (No manuscript counterpart.)
- `RayleighQuotient.lean` is a build-orphan the README cites as "Tier-1 min-max, zero sorry"; it proves one
  direction only. README overclaim (manuscript makes no min-max claim).

### Honest-failure clause — what was NOT reached
- **`SelfModelDeficitUnconditional/*` — NOW CHECKED (2026-05-27 follow-up):** found **UNSOUND** — the two
  axioms (`BekensteinInformationBound`, `NaturalityCoherence`) are logically inconsistent; `False` is derivable
  from each (verified, no `sorryAx`). Reclassified to **Category-B SEVERE** above (item 0 in the revision
  queue). No longer "not reached." The other `SelfModelDeficitRigorous/*` predicate-discharge files that feed
  it should get the same `∀`-quantifier check.
- `SelfRef/TraceInterior.lean`, `SelfModelDeficit/ZetaPrimeZero.lean` (axiomatized `zeta_F_prime_at_zero_visible`;
  README says superseded), `SelfModelDeficitRigorous/*`, `SigmaMPlHodgePeriod/{LemmaA,KunnethProof,PeriodCandidate,
  HiddenSectorProjection}` (headline routes around them, but their own axioms not individually audited),
  Cosmology `{SigmaTrDispersion, PerpetualTraceActivity, H4Nonlinear, EfoldMultiplicity}` — read at import
  surface only.
- `RayleighQuotient.lean` full min-max status could not be `#print axioms`-confirmed (no built olean; instructed
  not to `lake build`).
- The 1.28 MB manuscript was cross-checked at the cited theorem/line level, not exhaustively for every Tier tag.

**Distinguish "checked, clean" from "not reached":** the A-classifications above are *checked-clean* (read +
`#print axioms` where built); the four bullets in this clause are *not reached* and must not be assumed clean.
