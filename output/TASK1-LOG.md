# TASK1 — labels-only content-repair-2b log (2026-08-18)

Scope: REGISTER §2b sites listed in `output/PREREG.md` (the ~12 rows the
first repair never touched). Prose/docstring/STATUS only — no theorem
statement, proof term, `def` body, `axiom`, or numeric literal changed
except where an action explicitly records otherwise.

Classes used (frozen): SUBSTANTIVE / ARITHMETIC / DEFINITIONAL / SHELL.

Frozen actions: REPAIRED-SOUND / DEMOTED / RELABELLED / RETARGETED / LEFT-OPEN
(plus STALE-REGISTER for already-honest in-tree rows).

| file:line | decl name | class | action taken | old overclaim phrase stripped |
|---|---|---|---|---|
| SpectralPhysics/OffOrigin/DoddExistence.lean:141 | `record_transpose_invariant` | SUBSTANTIVE (semantic label only) | inherited cherry-pick `3b79a1f` / commit `19aed8c`, **verified** — docstring ORIENTATION→ARROW (A1) per `lem:polar-odd-sector`; decl/proof untouched | "blind to the orientation (transpose) bit" |
| SpectralPhysics/OffOrigin/MarkovCycle.lean:66 | `sigmaPReal` | DEFINITIONAL (semantic label only) | inherited, **verified** — docstring "orientation invariant"→"ARROW invariant (A1)" | "frame-relative orientation invariant" |
| SpectralPhysics/OffOrigin/OrientationLemma.lean:title | (module header) | — | inherited, **verified** — title + header note: instruments read ARROW (A1); Lean identifiers kept | "frame-relative orientation invariant σ_P" |
| SpectralPhysics/OffOrigin/OrientationLemma.lean:371 | `sigma_reads_sign` | SUBSTANTIVE (finite-dim LA) | inherited, **verified** — docstring adds ARROW (A1) reading note | (physical reading implied orientation) |
| SpectralPhysics/OffOrigin/EtaDirIndependence.lean:128 | `forward_origin` | SHELL (reduction; open via `loop_reads_arrow`) | **STALE register row** — already honest in-tree (`PROVED from loop_reads_arrow`; sorry sits on `loop_reads_arrow` at L123). No edit. | (register claimed "PROVED" over sorry — docstring already discloses the split) |
| SpectralPhysics/FaithfulnessForcesYR/CompositionFaithfulness.lean:100 | `jscSpectrumList_length` | ARITHMETIC | RELABELLED | "**Tier 1.** The JSC spectrum has length…" |
| SpectralPhysics/FaithfulnessForcesYR/CompositionFaithfulness.lean:106 | `jscSpectrumList_const` | DEFINITIONAL | RELABELLED | "**Tier 1.** Every entry of the JSC spectrum…" |
| SpectralPhysics/FaithfulnessForcesYR/CompositionFaithfulness.lean:118 | `compositeSpectrum_length` | ARITHMETIC | RELABELLED | "**Tier 1.** The composite spectrum has length…" |
| SpectralPhysics/FaithfulnessForcesYR/CompositionFaithfulness.lean:124 | `compositeSpectrum_injective_in_yR` | ARITHMETIC | RELABELLED + RETARGETED (cite DEGENERATE/NO L59) | "**Tier 1.** The composite spectrum… injective" |
| SpectralPhysics/FaithfulnessForcesYR/CompositionFaithfulness.lean:167 | `composition_faithful_at_every_yR` | SHELL | RELABELLED | "**Tier 1 — composition is faithful…" |
| SpectralPhysics/FaithfulnessForcesYR/CompositionFaithfulness.lean:59 | (file verdict C) | — | LEFT as DEGENERATE/NO (already honest); trunk L10611 → TRUNK-EDITS | (trunk "Tier 2: Framework theorem") |
| SpectralPhysics/FaithfulnessForcesYR/SelfModelDeficitFaithfulness.lean:102 | `jsc_eigenvalue_eq_majorana_scale` | DEFINITIONAL | RELABELLED | "**Tier 1.** The JSC eigenvalue equals…" |
| SpectralPhysics/FaithfulnessForcesYR/SelfModelDeficitFaithfulness.lean:115 | `visibleSpectrum` | SHELL (`:= []`) | RELABELLED | (implied measured spectrum) |
| SpectralPhysics/FaithfulnessForcesYR/SelfModelDeficitFaithfulness.lean:125 | `visibleSpectrum_independent_of_yR` | SHELL (`X=X:=rfl`) | RELABELLED | "**Tier 1 — visible spectrum is constant…" |
| SpectralPhysics/FaithfulnessForcesYR/SelfModelDeficitFaithfulness.lean:140 | `closure288Holds` | SHELL (`∃z,z=-288`) | RELABELLED | (implied fitted-spectrum theorem) |
| SpectralPhysics/FaithfulnessForcesYR/SelfModelDeficitFaithfulness.lean:149 | `closure288_holds_at_every_M_R` | SHELL/ARITHMETIC | RELABELLED | "**Tier 1 — the 288 closure holds…" |
| SpectralPhysics/FaithfulnessForcesYR/SelfModelDeficitFaithfulness.lean:157 | `closure288_does_not_pin_M_R` | SHELL | RELABELLED | "**Tier 1 — the closure does not pin…" |
| SpectralPhysics/FaithfulnessForcesYR/STATUS.md | Reading A/E / Sorries | — | RELABELLED + RETARGETED | "All theorems Tier 1"; "All Tier 1. No True placeholders" |
| SpectralPhysics/YukawaHierarchy/Bundle/SpectralAction.lean:39–46 | (module header) | DEFINITIONAL/ARITHMETIC + SHELL | RELABELLED | "Tier 1 conclusion y_c/y_τ = 3/16" |
| SpectralPhysics/YukawaHierarchy/Bundle/SpectralAction.lean:140 | `ratio_from_spectral_action_normalization` | DEFINITIONAL/ARITHMETIC | RELABELLED | "**Tier 1 — algebraic substitution**" |
| SpectralPhysics/YukawaHierarchy/Bundle/SpectralAction.lean:161 | `ratio_eq_three_sixteenths` | ARITHMETIC | RELABELLED | "**Tier 1 — algebraic corollary**" |
| SpectralPhysics/YukawaHierarchy/Bundle/SpectralAction.lean:178 | `bridgeConjecture_from_spectralAction` | SHELL/DEFINITIONAL | RELABELLED | "**Tier 1 — packaging instance**" |
| SpectralPhysics/YukawaHierarchy/Bundle/SpectralAction.lean:202 | `main_yukawa_ratio_theorem` | DEFINITIONAL/ARITHMETIC | RELABELLED | "**Tier 1 — algebraic substitution (top-level…" |
| SpectralPhysics/YukawaHierarchy/Bundle/SpectralAction.lean:235 | `normalization_iff_ratio` | DEFINITIONAL/ARITHMETIC | RELABELLED | "**Tier 1.** The framework's full normalization…" |
| SpectralPhysics/YukawaHierarchy/Bundle/ChernSimons.lean:80 | `ofPhysicalSM` | DEFINITIONAL (`⟨3⟩`) | RELABELLED | (implied computed CS integral) |
| SpectralPhysics/YukawaHierarchy/Bundle/ChernSimons.lean:153 | `BridgeConjecture.cs_value` | DEFINITIONAL (rfl) | RELABELLED | (cs_value always rfl) |
| SpectralPhysics/YukawaHierarchy/Bundle/ChernSimons.lean:116 | `doubleDynkin_SU3_in_16` | ARITHMETIC | **RELABELLED — review-lane fix.** Impl missed this row: the docstring still cited `SO10Decomposition.dynkin_SU3_in_16` (a `by decide` list-sum evaluation) as a "Tier 1 result" inside a site-list file. Retargeted to the ARITHMETIC class word. | "This is a Tier 1 result from `SO10Decomposition.lean`." |
| SpectralPhysics/YukawaHierarchy/Bundle/ChernSimons.lean:159 | `bridgeConjecture_implies_real_ratio` | SHELL | RELABELLED | "**Tier 1 / 3.**" |
| SpectralPhysics/YukawaHierarchy/Bundle/Pontryagin.lean:77 | `c2_BPST_SU3_eq_charge` | DEFINITIONAL | RELABELLED | "**Tier 1.** … equals its bundle charge" |
| SpectralPhysics/YukawaHierarchy/Bundle/Pontryagin.lean:81 | `c2_physicalSM_eq_charge` | DEFINITIONAL (`value:=charge`) | RELABELLED | "**Tier 1.** Same for the physical SM bundle" |
| SpectralPhysics/YukawaHierarchy/Bundle/Pontryagin.lean:116 | `bridge_numerator_via_c2` | DEFINITIONAL | RELABELLED | "**Tier 1 (organisational).** … = 3/16" |
| SpectralPhysics/YukawaHierarchy/Bundle/HeatKernelExpansion.lean:105 | `smFinData` | SHELL (`trace4=trace6:=0`) | RELABELLED **in the module header only** — the def's own docstring already carried the 2026-06-09 PLACEHOLDER NOTE and is byte-unchanged (review correction 2026-08-18) | (module header listed the file's content as Tier-1 without the placeholder caveat) |
| SpectralPhysics/YukawaHierarchy/Bundle/HeatKernelExpansion.lean:145 | `lambda2_at_framework_flat` | DEFINITIONAL | RELABELLED | "**Tier 1.** The Λ² coefficient…" |
| SpectralPhysics/YukawaHierarchy/Bundle/HeatKernelExpansion.lean:188 | `a2_from_lambda2` | ARITHMETIC/DEFINITIONAL | RELABELLED | "**Tier 1.** (1/6)·lambda2…" |
| SpectralPhysics/YukawaHierarchy/Bundle/HeatKernelExpansion.lean:202 | `heat_kernel_a2_matches` | SHELL | RELABELLED | "**Tier 1 — the heat-kernel-expansion bridge…" |
| SpectralPhysics/YukawaHierarchy/Bundle/HeatKernelExpansion.lean:213 | `lambda2_integer_near` | ARITHMETIC | RELABELLED | "**Tier 1 — final bridge**" |
| SpectralPhysics/YukawaHierarchy/Bundle/SpectralActionConcrete.lean:125 | `bridge_clean_form` | DEFINITIONAL/ARITHMETIC | RELABELLED | "**Tier 1 (clean form).** … y_c/y_τ = 3/16" |
| SpectralPhysics/YukawaHierarchy/Bundle/SpectralActionConcrete.lean:147 | `yukawa_ratio_from_spectral_structure` | SHELL/DEFINITIONAL | RELABELLED | "**Tier 1 — algebraic packaging**" |
| SpectralPhysics/Eta/IntegerCounts.lean:167 | `aps_bismut_freed_majorana_doubling` | ARITHMETIC/SHELL (`⟨2,rfl⟩`) | RELABELLED | "Named axiom: APS…"; "APS axiom" |
| SpectralPhysics/Eta/IntegerCounts.lean:172 | `apsFactor` / `apsFactor_eq_two` | DEFINITIONAL | RELABELLED | "extracted from the named axiom" |
| SpectralPhysics/EtaJSelfConj/EtaInvariant.lean:118 | `etaSum` | DEFINITIONAL (`A−A`) | RELABELLED | (Tier-1 η computation) |
| SpectralPhysics/EtaJSelfConj/EtaInvariant.lean:122 | `etaSum_eq_zero` | DEFINITIONAL | RELABELLED | "**Tier 1 — the structural cancellation**" |
| SpectralPhysics/EtaJSelfConj/EtaInvariant.lean:131–206 | `etaInvariant*` / `nuR_*` | DEFINITIONAL/ARITHMETIC | RELABELLED | "**Tier 1.** …" (multiple) |
| SpectralPhysics/IndexJSelfConj/JSelfConjBlock.lean:163 | `dim_Cl06_irrep_eq_eight` | ARITHMETIC/SHELL (`8=8`) | RELABELLED | (Lawson–Michelsohn citation framing; already partly honest) |
| SpectralPhysics/IndexJSelfConj/JSelfConjBlock.lean:41–212 | decide/rfl counts + re-exports | ARITHMETIC/DEFINITIONAL/SHELL | RELABELLED | "**Tier 1**" / header Tier-1 list |
| SpectralPhysics/Algebra/Forcing.lean:242 | `forcing_contains_octonions` | SHELL (`True:=trivial`) | RELABELLED | (implied Forcing Theorem) |
| SpectralPhysics/Conjectures/Hodge.lean:425 | `voisin_counterexample_is_below_threshold` | SHELL (`True:=trivial`) | RELABELLED | (implied Voisin theorem) |
| SpectralPhysics/Algebra/CirculantMatrix.lean:30 | (module header Koide) | LEFT-OPEN | RELABELLED | "The Koide ratio K … = 2/3 follows…" |
| SpectralPhysics/Algebra/CirculantMatrix.lean:106 | `koide_from_circulant` | LEFT-OPEN (`sorry`) | RELABELLED | "**Koide formula … K = 2/3**" over sorry |
| SpectralPhysics/Algebra/CirculantMatrix.lean:124 | `circulant_sqrt_sum_identity` | LEFT-OPEN (`sorry`) | RELABELLED | "deep reason Koide works … ratio 2/3" |
| SpectralPhysics/OffOrigin/EtaDirIndependence.lean:126 + STATUS.md | `forward_origin` prose | SHELL | RELABELLED (PROVED-token hygiene `670abeb`) | "PROVED from loop_reads_arrow" → "discharged in-body from…" |


## Review-lane addenda (2026-08-18)

* **Residual `Tier 1` tokens in site-list files after the impl pass** — enumerated
  and adjudicated, not left silent:
  * `Bundle/ChernSimons.lean:116` — **live overclaim over a `decide` decl. FIXED**
    (row added above).
  * `Bundle/SpectralAction.lean:47`, `FFYR/CompositionFaithfulness.lean:101` — the
    token appears inside a *negation* ("do not cite as Tier 1"). Correct as written;
    no edit.
  * `OffOrigin/DoddExistence.lean:25,524` — "at Tier 1" names the rigor tier of
    `dodd_exists`, whose term is an explicit two-matrix witness (not
    `rfl`/`decide`/`True`/hypothesis-restatement) and whose `#print axioms` is
    `[propext, Classical.choice, Quot.sound]` — **SUBSTANTIVE**, so the Task-1
    trigger does not fire. No edit.
* **`Tier 1` outside the site-list files** (`EtaJSelfConj/APSIndex.lean`,
  `SpectralFlow.lean`, `Verdict.lean`, `IndexJSelfConj/ExponentVerdict.lean`,
  `IndexComputation.lean`, `STATUS.md`, `FFYR/AxiomThreeRestricted.lean`,
  `CDTowerExtension.lean`, `OperatorReconstruction.lean`, `Bundle/AtiyahSinger.lean`,
  `Curvature.lean`, `InstantonNumber.lean`, `THooftSymbol.lean`) — **out of Task-1
  scope** (the spec scopes to site-list decls "and every decl in the same file") and
  outside success-criterion 4's grep vocabulary. Carried to Open Questions as the
  natural §2c follow-up, not silently absorbed.
* **`CLOSED` tokens in `OffOrigin/STATUS.md` / `ForwardOriginSplit.lean` /
  `DoddExistence.lean`** — sit on decls with real proof terms and are not in
  criterion 4's grep vocabulary. Left as-is; flagged for the follow-up sweep.
* **Positive control** — `output/hostile/ClassAudit2b.lean` (+ `.out`) re-derives the
  class of every site-list decl independently of the docstrings: `#print axioms` on
  each, plus `rfl` / `decide` / `⟨_, rfl⟩` witnesses that *compile only if* the decl
  really carries the shell/arithmetic/definitional class now claimed. All fired.
