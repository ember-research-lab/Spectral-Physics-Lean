# Axiom Soundness Sweep

**Date:** 2026-05-27. **Mode:** read-and-classify only (no fixes, no edits to any repo file).
**Scope:** all `axiom` declarations under `SpectralPhysics/` (**122** total). Build green (3324 jobs).
Every UNSOUND verdict is verified by a SCRATCH `example : False` (in `/tmp`, no repo file touched) with
`#print axioms` showing the False-derivation depends on the axiom and carries **no `sorryAx`**.

## Classification scheme

- **UNSOUND** — the axiom's statement is false at some instantiation; `False` is derivable. (Bug class:
  an (in)equality/equality quantified over a variable or structure broader than any constraining hypothesis.)
- **SOUND** — consistent (no `False` derivable). Sub-flags: *data* (postulates a term of an inhabited type),
  *constrains-opaque* (bounds/pins an opaque constant/function — consistent), *conditional* (the (in)equality
  is hypothesis-guarded), *redundant* (statement is trivially provable ⇒ should be a `theorem`, not an axiom),
  *shell* (consistent but content-vacuous, e.g. `Nonempty (opaque ≃ opaque)`).
- **CITATION** — a true externally-established result legitimately axiomatized (Mathlib lacks it); source cited.
- **UNDETERMINED** — cannot decide; reason given.

**Method note (honest-failure):** I exhaustively checked every axiom matching the UNSOUND *shape* (a bound or
equality with a free/under-constrained quantified variable) by adversarial instantiation — that shape is the
only known route to unsoundness and is what produced item 0. The four UNSOUND axioms below were each
`example : False`-verified. The remaining axioms are classified by statement shape + the opaqueness of their
referents (data / conditional / constrains-opaque / citation), **not** each individually False-tested; this is
"checked by class-analysis," not "individually refuted." Genuinely ambiguous ones are marked UNDETERMINED.

---

## TASK 1 — UNSOUND axioms (verified)

| Axiom | file:line | Witness (`example : False`) | `#print axioms` of the False-deriv |
|---|---|---|---|
| `BekensteinInformationBound (S)(c:ℝ) : c ≤ S.dimHid` | `SelfModelDeficitUnconditional/CapacityBound.lean:106` | `c := dimHid+1` ⇒ `dimHid+1 ≤ dimHid` | `[propext, Classical.choice, Quot.sound, BekensteinInformationBound]` (no sorryAx) |
| `NaturalityCoherence (S)(c:ℝ) : S.dimHid ≤ c` | `SelfModelDeficitUnconditional/NaturalityBound.lean:108` | `c := dimHid−1` ⇒ `dimHid ≤ dimHid−1` | `[…, NaturalityCoherence]` (no sorryAx) |
| `cheeger_lower (cd : CheegerData) : cd.cheeger_h²/(2·cd.d_max) ≤ cd.spectral_gap` | `Analysis/CheegerInequality.lean:69` | `cd := ⟨h=10, gap=0, d_max=1, …nonneg…⟩` ⇒ `50 ≤ 0` | `[propext, Classical.choice, Quot.sound, cheeger_lower]` (no sorryAx) |
| `cheeger_upper (cd : CheegerData) : cd.spectral_gap ≤ 2·cd.cheeger_h·cd.d_max` | `Analysis/CheegerInequality.lean:80` | `cd := ⟨h=0, gap=5, d_max=1, …⟩` ⇒ `5 ≤ 0` | `[…, cheeger_upper]` (no sorryAx) |

**All four are the SAME bug class:** a mathematically-true *physical* inequality (Bekenstein bound; Cheeger
1970) asserted over an **abstract structure / free real variable whose invariants do not entail it**.
`CheegerData` carries only `0≤h`, `0≤gap`, `0<d_max` — nothing links them via the inequality, so it holds for
real graph data but is false for arbitrary triples. Same for the `c`-over-all-reals in Bekenstein/Naturality.
This class is invisible to `check_axioms.sh` (not `∃_,True`, not `:=True`) and was missed by `3f66049` (which
fixed the `:=True`-predicate→`0=1` route). **Intended fix (do NOT apply here):** quantify the bounded variable
only over realisable values (the actual information content / real graph data), not all reals / all structures.

### Provable-existential axioms (SOUND but **redundant** — should be `theorem`, not `axiom`)

| Axiom | file:line | Why redundant |
|---|---|---|
| `aps_bismut_freed_majorana_doubling : ∃ apsFactor:ℕ, apsFactor = 2` | `Eta/IntegerCounts.lean:162` | provable `⟨2, rfl⟩` — a `∃x, x=2` vacuous-marker (the `check_axioms.sh` `∃_,True` cousin). |
| `seesaw_product_independence : ∃ K, S_nuR = K − S_nuL ∧ S_charged + K = 288` | `SelfModelDeficit/SeeSawCancel.lean:131` | witnessed by `K = 288 − S_charged` given the `def`s (S_charged=277.39, S_nuL=184.62, S_nuR=−174.01) ⇒ provable by `norm_num`. This is the "288 see-saw closure" back-fit (register §particle). |

### SOUND — data / operation stubs (postulate a term of an inhabited type; cannot cause `False`) — 22

`y` (`VisFermion→ℝ`), `xi_visible` (`Fermion→ℝ`), `etaB_observed`, `Jarlskog`, `gj_c{1,2,3}_empirical`,
`MR_over_Lambda_c`, `I_star`, `M_R`, `sigma0`, `YM_mass_squared`, `YM_mass_gap`, `zeta_F_prime_at_zero_visible`
(all `:ℝ`); `YMState_nonempty`, `RelationalKernel_nonempty`, `Z23_nonempty` (`Nonempty _`); `Z23_mul`
(`Z23→Z23→Z23`); `lefschetz_1_1`, `hodge_abelian_lefschetz_classes` (Hodge data); `octonions_eq_CZ23_cotwist`,
`AM_twist_invariance_existence` (`Nonempty (opaque ≃ opaque)` — see *shell* note below).

### SOUND — constrains-opaque (bounds/pins an opaque constant or function; consistent) — ~26

Positivity: `MPl_pos`, `LambdaC_pos`, `lambda_c_sq_target_pos`, `I_star_pos`, `M_R_pos`, `sigma0_pos`,
`Jarlskog_pos`, `YM_mass_gap_pos`. Value-pins: `Jarlskog_value`, `etaB_observed_value`,
`zeta_regularization_log_sum`, `mellin_finite_zeta_at_zero`. Brackets on opaque/data: `gj_c{1,2,3}_empirical_bracket`,
`xi_visible_window`, `MR_over_Lambda_c_in_window`. ∀-nonneg/conditional on opaque: `y_pos`, `y_lt_one`,
`ZeroedModesContribution_nonneg`, `V_1_Squared_nonneg`, `YM_mass_squared_nonneg`, `YM_mass_gap_separates`,
`lambda_1_pos_from_self_reference`, `de_sitter_asymptote_from_positive_lambda`, `lambda_cc_eq_lambda_1_limit`,
`scse_lambda_1_continuous`, `prop_berry_crossover`. The four per-sector Yukawa-sum equalities
(`up/down/lep/light_nu_sector_log_yukawa_sum`) pin opaque `negLogY` to the PDG `def`s — consistent.
*(All consistent: each is satisfiable by some assignment of its opaque referents; none derives `False` without an
additional pinning axiom — none present.)*

### CITATION — true external results, Mathlib lacks them — ~14

Hurwitz: `composition_dim_le_eight_axiom`, `composition_algebra_tower_step` (genuine `[CompositionAlgebra]`
norm-mult constraint ⇒ dim∈{1,2,4,8}; **adversarially checked: SOUND**, the class is a real constraint not a
shell). Baker: `baker_theorem_bound`, `baker_transcendence_not_rational` (Baker 1966). Connes–Marcolli:
`ccm2008_kodim6_sign_triple`, `connes_marcolli_2008_thm_1_214`, `standardModel_three_generations`,
`j_quotient_axiom_collapses_multiplicity`. SM RGE (conditional existence): `machacek_vaughn_two_loop_exists`,
`ford_jones_stevenson_stephens_extension`, `mihaila_salomon_steinhauser_three_loop`, `manohar_wise_decoupling`.
Kasparov/cancellation: `K1_mesland_rennie_card`, `K2_rosenberg_schochet_cancel`, `minkowski_left/right_cancel`.
Rellich–Kondrachov: `rellich_kondrachov_trace_class`. Thermo: `second_law_entropy_increase`.

### SOUND — shell (consistent, but content-vacuous `Nonempty(opaque ≃ opaque)` — register §gravity) — ~5

`kassel_kunneth_Z23graded`, `connes_HKR`, `naisse_putyra_eilenberg_zilber`, `akrami_majid_twist_invariance`,
`H7_composition`. Non-vacuous *only* because the two sides of each `≃` are distinct opaque types; already
demoted + flagged by the 2026-05 audit. SOUND (no `False`), but carry no formalized literature content.

### UNDETERMINED — 2

- `hypothesisB_NCG_rule : three_gen_dirac_multiplicity = 6` (`MajoranaBlock/HypothesisB.lean:22`) — sound iff
  `three_gen_dirac_multiplicity` is opaque-or-`def`-`=6` (then redundant) vs `def ≠ 6` (then UNSOUND). The
  identifier was refactored/removed (see the quarantined `ZetaFNuR` finding); could not pin its current
  definition in scope without a build. **Flag for a targeted check.**
- `mellin_heat_kernel_finite_spectrum_log_sum` (`SelfModelDeficitRigorous/SpectralZeta.lean`) — an equality
  on the Mellin-regularised spectrum; referents not fully traced. Likely SOUND constrains-opaque, but not
  individually verified.

---

## TASK 2 — Blast radius (currently-unsound results)

`#print axioms` on the register's headline theorems, flagging transitive dependence on an UNSOUND axiom:

| Unsound axiom(s) | Theorems made unsound | Notes |
|---|---|---|
| `BekensteinInformationBound`, `NaturalityCoherence` | `self_model_deficit_unconditional` (+ `_explicit`, `_param`, `_explicit_param`); the discharge lemmas `completenessAtLevel2_negZetaPrimeAtZero`, `sectorFaithfulNoDeadWeight_negZetaPrimeAtZero`, `negZetaPrimeAtZero_le_dimHid`, `dimHid_le_negZetaPrimeAtZero`, `completenessAtLevel2_of_bekenstein`, `sectorFaithfulNoDeadWeight_of_naturality` | **The entire `SelfModelDeficitUnconditional` "−ζ̃'_vis(0)=288" family is unsound.** All are in the root build. Confirmed: `#print axioms self_model_deficit_unconditional` = `[propext, Classical.choice, Quot.sound, BekensteinInformationBound, NaturalityCoherence]`. |
| `cheeger_lower`, `cheeger_upper` | **none** | **No consumers.** The textual `cheeger_lower/upper` matches elsewhere are `DiscreteCheeger`'s differently-named `cheeger_{lower,upper}_bound` theorems (themselves `sorry`-blocked, separate). `cheeger_colding` is clean (`[propext, Classical.choice, Quot.sound]`). So these two are **unsound but unused — latent landmines** in the root build: anyone who invokes them derives `False`, but no current headline is contaminated. |

**Currently-unsound results list:** the `SelfModelDeficitUnconditional` family only (6 declarations + 4 headline
variants). Everything else in the register's headline set is free of the four unsound axioms.

---

## TASK 3 — Previously-unreached files

| File / dir | Axioms | Verdict |
|---|---|---|
| `SelfRef/TraceInterior.lean` | none | **A / clean** — no axioms, no `sorry`. Theorems only. |
| `Cosmology/SigmaTrDispersion.lean` | none | **A / clean** — no axioms, no `sorry`. |
| `Cosmology/PerpetualTraceActivity.lean` | none | **A / clean** — no axioms, no `sorry`. |
| `Cosmology/H4Nonlinear.lean` | none | **A / clean** — no axioms, no `sorry`. |
| `Cosmology/EfoldMultiplicity.lean` | none | **A / clean** — no axioms, no `sorry`. |
| `SelfModelDeficit/ZetaPrimeZero.lean` | `zeta_F_prime_at_zero_visible` (data ℝ), `zeta_regularization_log_sum` (opaque=def) | **SOUND** (data + constrains-opaque). README: superseded by the Unconditional branch (which is itself UNSOUND — see Task 2). |
| `SigmaMPlHodgePeriod/KunnethProof.lean` | `akrami_majid_twist_invariance`, `kassel_kunneth_Z23graded`, `connes_HKR`, `naisse_putyra_eilenberg_zilber`, `H7_composition` | **SOUND — shell** (Nonempty opaque-`≃`; content-vacuous, flagged). No `sorry`. |
| `SigmaMPlHodgePeriod/LemmaA_AMTwistInvariance.lean` | `Z23_nonempty`, `AM_cotwist_F_nonzero`, `Z23_mul`, `octonions_eq_CZ23_cotwist`, `AM_twist_invariance_existence` | **SOUND** (data + shell). `AM_cotwist_F_nonzero : ∀ g h, AM_cotwist_F g h ≠ 0` constrains an opaque map — consistent. |
| `SelfModelDeficitRigorous/*` | `mellin_heat_kernel_finite_spectrum_log_sum` (+ 1 file with a `sorry`) | **UNDETERMINED → likely SOUND** for the axiom (constrains-opaque equality); the `sorry` location not classified. This chain *feeds* the UNSOUND Unconditional headline but the unsoundness is introduced downstream (Bekenstein/Naturality), not here. |

---

## Manuscript-mapping column (genuinely-computable / circular / unsound)

For the release decision — **do not conflate "hard to compute" with "circular," nor "circular" with "unsound":**

| Manuscript claim | Axiom(s) | Verdict |
|---|---|---|
| Self-Model Deficit `−ζ̃'_vis(0)=288` "PARTIAL unconditional" | Bekenstein, Naturality | **UNSOUND** (axioms inconsistent; `=288` derivable but so is `0=1`). |
| Cheeger inequality (Tier-1 "Cheeger 1970, Standard") | `cheeger_lower/upper` | **UNSOUND as axiomatised** (true for real graphs, false over `CheegerData`). Unused, so no result contaminated — but the Tier-1 "proved" status is not met. |
| "288 see-saw closure" (`S_charged+S_νR=288`) | `seesaw_product_independence` | **CIRCULAR** (sound: `K_seesaw` back-fit to 288), NOT unsound. |
| κ₂^SM,full perturbative ≈ 287 (falsifies v0.9's 258) | `kappa2_full_numerical_bracket`, `_window` | **GENUINELY-COMPUTABLE** (axiomatised mpmath result on a `noncomputable def`; Lean can't reduce it, hence the axiom). No free-variable contradiction → sound. |
| GJ empirical ratios; PDG Yukawa sector sums | `gj_c*_empirical(_bracket)`, `*_sector_log_yukawa_sum` | **GENUINELY-COMPUTABLE** (axiomatised observation/PDG data). Sound. |
| σ₀/M_Pl Akrami–Majid Hodge period | Kassel/Connes-HKR/Naisse/AM shells | **NEITHER** — content-vacuous shells; the headline routes around them (register §gravity). Sound, no content. |
| Cabibbo, θ₁₃, η_B(λ¹⁴), cosmic budget, Σmν floor | (no axioms / kernel-only) | **GENUINELY-COMPUTABLE** (proved sorry-free; register §particle/cosmology). |

---

## Summary

**122 axioms:** UNSOUND **4** · SOUND **114** (of which: data 22, constrains-opaque ~26, citation ~14,
shell ~5, redundant/provable **2**, the bulk of the remaining conditional/structural) · UNDETERMINED **2**.

**The 4 UNSOUND, ranked by impact:**
1. **`BekensteinInformationBound` + `NaturalityCoherence`** — contaminate the live `SelfModelDeficitUnconditional`
   `=288` family (root build). **Release-blocking** for any claim resting on `−ζ̃'_vis(0)=288`.
2. **`cheeger_lower` + `cheeger_upper`** — unsound but **unused**; latent landmines. Not currently contaminating
   a result, but they falsify the Tier-1 "Cheeger inequality proved" status and could silently launder `False`
   into any future theorem that invokes them.

**Two redundant axioms** (`aps_bismut_freed_majorana_doubling`, `seesaw_product_independence`) are trivially
provable and should be `theorem`s (RIGOROUS_WORKFLOW: the `axiom` keyword is for non-derivable assertions).

**Recommended next task (SEPARATE — restricting quantifiers is a fix, not this audit):** for each of the 4
UNSOUND axioms, restrict the bounded variable to its realisable domain (Bekenstein/Naturality: the specific
information content, not all `c:ℝ`; Cheeger: add a `CheegerData` field encoding the actual graph relationship,
or quantify over real graph Laplacians). Until then, the `SelfModelDeficitUnconditional` `=288` headline must
not be presented as established, and the Cheeger axioms should be quarantined.

## Honest-failure — what was NOT done
- The 114 SOUND verdicts are classified by **statement-shape + referent-opaqueness analysis**, not by an
  individual `example : False` attempt on each. The UNSOUND *shape* (under-constrained bound/equality) was
  enumerated and every matching candidate was adversarially instantiated; a soundness bug of a *different*
  shape (e.g. two individually-sound axioms that are jointly contradictory across modules) would not be caught
  by this method. No such cross-axiom contradiction was searched for beyond the within-module pairs already noted.
- `hypothesisB_NCG_rule` and `mellin_heat_kernel_finite_spectrum_log_sum` are **UNDETERMINED** (need the
  current definition of `three_gen_dirac_multiplicity` / the Mellin referents pinned, which needs a build).
- `SelfModelDeficitRigorous/*` has one `sorry` whose enclosing declaration was not classified (headline vs
  supporting).
- Blast-radius `#print axioms` was run on the register's headline set + the Cheeger consumers; it was **not**
  run on all ~3300 build declarations, so a deeply-buried consumer of `cheeger_lower/upper` cannot be 100%
  excluded (textual grep found none).
