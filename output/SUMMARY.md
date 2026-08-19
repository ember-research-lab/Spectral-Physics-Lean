# SUMMARY — lean-content-repair-2b (FINAL)

**Date:** 2026-08-18
**Branch:** `fix/lean-content-repair-2b-2026-08-18` (from `main` @ `4d70853`)
**Status:** All 5 directory groups committed; full `lake build SpectralPhysics` clean (3356 jobs); overclaim grep clean on touched dirs; `sorry` count unchanged; axiom-name set unchanged. Numbers below re-derived by the review lane (the impl's counts used a narrower regex).

Checkpoint `SUMMARY.md` was written mid-budget after directories 1–4 (before the
Algebra trio) per the impl's report. **Review note:** this is *not independently
verifiable* — `output/` is untracked (`.gitignore` does not cover it, but it was
never added), so only the final mtimes survive and no earlier revision exists.
Recorded as impl testimony, not as a verified fact.

## Directive Gate — re-assertion (final)

- **2026-08-04 (no volume):** one branch; no new Lean modules created.
- **2026-08-13 (no new consolidation doc):** deliverable is
  `output/DECL-CLASS-MANIFEST-2b.json` (machine JSON) + this SUMMARY.
- **2026-08-12:** N/A.
- **2026-08-16 representation clause:** OffOrigin ORIENTATION→ARROW (A1) applied
  per `lem:polar-odd-sector` (Θ-parity / σ_P instruments read the ARROW, not A4
  orientation). Not re-litigated. Cherry-pick `3b79a1f` → `19aed8c` verified
  against the site list; PROVED-token hygiene follow-up `670abeb`.

## Directory commits

| # | Group | Commit | PROPOSED frozen branch |
|---|---|---|---|
| 1 | OffOrigin | `19aed8c` (+ `670abeb` PROVED-token) | **RELABELLED** (semantic ARROW); EtaDirIndependence:128 **STALE-REGISTER** |
| 2 | FaithfulnessForcesYR | `db4048b` | **RELABELLED** (+ STATUS **RETARGETED**) |
| 3 | YukawaHierarchy/Bundle | `fbacb78` | **RELABELLED** |
| 4 | Eta / EtaJSelfConj / IndexJSelfConj | `4aaacb5` | **RELABELLED** |
| 5 | Algebra/Forcing + Conjectures/Hodge + CirculantMatrix | `ca198c5` | **RELABELLED**; CirculantMatrix Koide **LEFT-OPEN** (`sorry` unchanged) |

## Per-site PROPOSED branches (review owns final)

1. **OffOrigin** — RELABELLED. Instruments DoddExistence L141 / MarkovCycle L66 /
   OrientationLemma title+`sigma_reads_sign` → ARROW (A1).
   `EtaDirIndependence:128` STALE-REGISTER (already honest split; PROVED token
   removed for grep hygiene only).
2. **FFYR** — RELABELLED. File verdicts DEGENERATE/NO preserved. Shells
   `visibleSpectrum:=[]`, `closure288Holds:=∃z,z=-288` classed SHELL.
   Trunk L10611 → see `TRUNK-EDITS-2b.md` row 1 (reinforces first-run row 4).
3. **YukawaHierarchy/Bundle** — RELABELLED. Header no longer claims Tier-1
   `y_c/y_τ=3/16`; ratio decls DEFINITIONAL/ARITHMETIC; `cs_value` /
   `c2.value:=charge` DEFINITIONAL; `trace4=trace6:=0` SHELL.
4. **Eta / EtaJ / IndexJ** — RELABELLED. APS `⟨2,rfl⟩` ARITHMETIC/SHELL;
   η-sum `A−A` DEFINITIONAL; `8=8` ARITHMETIC/SHELL.
5. **Algebra trio** — Forcing / Hodge `True:=trivial` SHELL RELABELLED;
   CirculantMatrix Koide docstring LEFT-OPEN over existing 2 `sorry` (no new
   sorry).

## UNSOUND / hostile files

**None UNSOUND.** No site presented a universally quantified free-structure axiom
of the U1/U2/U7/U8/U9 shape; the axiom-name set is unchanged and no decl proves
`False`. All sites are shells / arithmetic / definitional / LEFT-OPEN `sorry`.

The impl wrote no `output/hostile/` file (PREREG: shells need no hostile witness).
The **review lane wrote one anyway** as a positive control, because "the class is
read from the term" is a claim that should itself be machine-checked:
`output/hostile/ClassAudit2b.lean` (output in `ClassAudit2b.out`). It

* `#print axioms` every site-list decl, and
* supplies `rfl` / `decide` / `⟨_, rfl⟩` witnesses that **compile only if** the decl
  really is the shell the docstring now claims — a genuine positive control, since a
  substantive decl would fail to elaborate them.

Re-derived results (review lane, not inherited):

| decl | `#print axioms` | class confirmed |
|---|---|---|
| `Eta.IntegerCounts.aps_bismut_freed_majorana_doubling` | *no axioms* | ARITHMETIC/SHELL (`⟨2, rfl⟩` fires) |
| `IndexJSelfConj.dim_Cl06_irrep_eq_eight` | *no axioms* | ARITHMETIC/SHELL (`8 = 8 := rfl` fires) |
| `IndexJSelfConj.jsc_total_majorana_count_eq_six` | *no axioms* | ARITHMETIC (`by decide` fires) |
| `forcing_contains_octonions` | *no axioms* | SHELL — `#check` prints `(∀ n < 8, True) → (∀ n, 16 ≤ n → True) → True`: hypotheses *and* conclusion are `True` |
| `voisin_counterexample_is_below_threshold` | propext, Classical.choice, Quot.sound | SHELL — conclusion is `True` |
| `Bundle.ChernSimons3Form.ofPhysicalSM_value` / `c2_physicalSM_eq_charge` | clean | DEFINITIONAL (`= 3 := rfl`, `value = charge := rfl` both fire) |
| `FFYR.closure288_holds_at_every_M_R` / `visibleSpectrum_independent_of_yR` | clean | SHELL (`⟨-288, rfl⟩` and `visibleSpectrum = [] := rfl` fire) |
| `EtaJSelfConj.etaSum_eq_zero`, `nuR_etaInvariant_ne_eight` | clean | DEFINITIONAL / ARITHMETIC |
| `Bundle.main_yukawa_ratio_theorem` | clean | DEFINITIONAL/ARITHMETIC (hypothesis restatement) |
| `CirculantMatrix.koide_from_circulant` | **sorryAx** | LEFT-OPEN ✔ |
| `OffOrigin.forward_origin` | **sorryAx** | LEFT-OPEN via `loop_reads_arrow` — which is exactly why the old **PROVED** token was an overclaim and `670abeb` is justified |
| `OffOrigin.dodd_exists`, `record_transpose_invariant` | clean | SUBSTANTIVE (control: these are *not* rfl-dischargeable) |

## Build / invariants

- `lake build SpectralPhysics`: **clean** (3356 jobs), post-all-edits *and* after
  the review-lane ChernSimons fix.
- `sorry` occurrences (`git grep -cE '^[[:space:]]*sorry([[:space:]]|$)'` over
  `SpectralPhysics/`): base **13** = HEAD **13**. (The impl reported 9 = 9 using a
  stricter `^\s*sorry\s*$`; both regexes agree the count is unchanged.)
- `axiom` declarations (`^axiom <name>`): base **114** = HEAD **114**, name-for-name
  identical. (The impl reported 100 = 100; the raw line-start grep also picks up one
  docstring line beginning "axiom was …" that a 2b docstring rewrite deleted — that
  is prose, not a declaration.)
- `git grep -E 'closed via|machine-checked|PROVED|NON-VACUOUS'` on the touched dirs:
  **empty** (verified by the review lane with correct pathspec word-splitting — an
  unquoted `$D` under zsh silently matches nothing, so re-run it as
  `set -- <paths>; git grep -E … -- "$@"`).
- **Only comments changed.** A comment-stripping diff of every touched `.lean` file
  between `main` and `HEAD` is empty: no theorem statement, proof term, `def` body,
  `axiom`, or numeric literal moved. This is the machine check behind
  "labels and soundness only".

## Artefacts

| File | Role |
|---|---|
| `output/PREREG.md` | Sealed Directive Gate + site list |
| `output/TASK1-LOG.md` | Per-decl table (site list + siblings) |
| `output/TRUNK-EDITS-2b.md` | Proposed monograph/trunk retags (NOT applied) |
| `output/DECL-CLASS-MANIFEST-2b.json` | Touched-file decl scan |
| `output/SUMMARY.md` | This file (final; mid-budget checkpoint per impl testimony — see note at top) |
| `output/hostile/ClassAudit2b.lean` / `.out` | Review-lane positive control: `#print axioms` + `rfl`/`decide` class witnesses |

## Trunk-edit list (pointer)

See `TRUNK-EDITS-2b.md`: L10611 FFYR; Bundle HeatKernelExpansion L6330;
v7 `thm:charm-tau` (~3371); v0.9 Δη / η / Clifford-8 headlines; Koide sorry.
No `spectral-physics.tex` edits in this run.


## Review-lane changes (2026-08-18, session `2bb62781`)

Adjudicated independently of the impl's proposals; the branches above survived
re-derivation, with these corrections:

1. **`Bundle/ChernSimons.lean:116` — missed site row, FIXED.** The docstring on
   `doubleDynkin_SU3_in_16` still read *"This is a Tier 1 result from
   `SO10Decomposition.lean`"*, citing `dynkin_SU3_in_16 : doubleDynkinSum = 4 :=
   by decide`. That is a live Tier-1 tag over a `decide` decl **inside a site-list
   file**, i.e. squarely inside Task 1's trigger. Relabelled to **ARITHMETIC**.
2. **`DECL-CLASS-MANIFEST-2b.json` regenerated.** The impl scanner was a
   comment-blind regex: it emitted 216 `UNCLASSIFIED` rows including English words
   lifted out of docstrings (`{"name": "of", "kind": "class"}`, `"is"`, `"and"`,
   `"that"`, `"for"`), and it predated commit `670abeb`, so
   `OffOrigin/EtaDirIndependence.lean` was **absent entirely**. The manifest is now
   produced by a comment-aware scanner over all **17** touched `.lean` files
   (**256** decls, no prose artefacts), and it records **before *and* after**
   docstring sha — the impl had only captured "after", so `RELABELLED` was an
   assertion rather than a computed fact. It is now derived from
   `sha(before) ≠ sha(after)`.
3. **`TASK1-LOG.md`** — a stray blank line had split the table into two markdown
   tables; the `smFinData` row claimed a def-docstring edit that did not happen (the
   2b change was in the module header; the def's own 2026-06-09 PLACEHOLDER NOTE is
   byte-unchanged); the ChernSimons row above was missing. All three corrected, and
   a Review-lane addenda section enumerates every residual `Tier 1` / `CLOSED` token
   with its adjudication.
4. **Positive control added** — `output/hostile/ClassAudit2b.lean` / `.out`
   (see above). The impl's "shells need no hostile file" reading is defensible under
   the PREREG, but G6 ("a silent compile is not evidence") is better served by a
   witness that *fires*.
5. **Invariant counts re-derived** and the impl's narrower numbers annotated rather
   than overwritten.

### Not changed (deliberately)

* Residual `Tier 1` in **non-site** files of the touched directories (13 files) —
  outside Task 1's stated scope and outside criterion 4's grep vocabulary. Logged as
  the §2c follow-up rather than absorbed silently.
* `EtaDirIndependence.lean`'s PROVED-token edit (`670abeb`) **kept**, though the
  PREREG said "no edit" for that STALE row. Success criterion 4 requires the `PROVED`
  grep to be empty across the touched dirs, and `#print axioms forward_origin`
  returns `sorryAx` — so "PROVED" was an overclaim on the merits. Recorded as a
  disclosed, justified PREREG deviation, not a silent one.
