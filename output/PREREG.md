# PREREG — lean-content-repair-2b (2026-08-18)

Sealed at the start of implementation, before Task 1 edits beyond the inherited
OffOrigin cherry-pick. This file is not edited after sealing except to append
BEFORE/AFTER rows of the positive-control table once any UNSOUND site is
witnessed — those additions are timestamped inline and are pure recording.

## Directive Gate

- **2026-08-04 (no volume):** one branch, no new modules. Honored: all work is on
  branch `fix/lean-content-repair-2b-2026-08-18` inside the existing
  `SpectralPhysics/` tree at
  `/home/aaron/spectral-physics-manuscript/lean`. No new `.lean` module files.
  Bookkeeping artifacts live under `output/` only.
- **2026-08-13 (no new consolidation doc):** the deliverable
  `output/DECL-CLASS-MANIFEST-2b.json` is machine JSON, not a prose consolidation
  document. `SUMMARY.md` is the spec-required summary.
- **2026-08-12:** N/A (not applicable to this spec).
- **2026-08-16 representation clause (OffOrigin):** the OffOrigin
  ORIENTATION→ARROW row is a *semantic* relabel per `lem:polar-odd-sector`.
  Θ-parity / σ_P instruments read the ARROW (A1), not the orientation (A4).
  **Rule applied:** rewrite docstring / STATUS labels that say ORIENTATION on
  those instruments to ARROW (A1). Do not re-litigate the manuscript lemma;
  do not change decl statements or proof terms for this row.

## Frozen vocabulary (per site)

Same definitions as the first repair's PREREG:

- **REPAIRED-SOUND** — axiom replaced by a hypothesis or pinned to a concrete
  object; hostile witness now fails to compile (or fails to derive `False` /
  its designed positive claim).
- **DEMOTED** — moved to `Conjectures/` or renamed `placeholder_*` (or
  axiom→def/theorem when trivially provable outright).
- **RELABELLED** — docstring/STATUS/README corrected to the decl's true class;
  decl statement and proof unchanged.
- **RETARGETED** — downstream citation moved from a shell/arithmetic decl to
  the honest decl (or STATUS row) that carries the claimed content.
- **LEFT-OPEN** — recorded with an explicit reason; complete deliverable.

## Frozen class words

SUBSTANTIVE / ARITHMETIC / DEFINITIONAL / SHELL.

## Site list (REGISTER §2b + REPORT.md criterion 3)

Each row quotes the register's claim. Frozen branch per site is filled in
SUMMARY.md after work; here only the preregistered target is named.

1. **OffOrigin** — `OffOrigin/DoddExistence.lean:141`, `MarkovCycle.lean:66`,
   `OrientationLemma.lean` (title, `sigma_reads_sign`) — ORIENTATION labels on
   Θ-parity / σ_P instruments → ARROW (A1).
   `EtaDirIndependence.lean:128` is a **STALE register row** — already honest
   in-tree; record as such, no edit. Inherited cherry-pick
   `3b79a1f` / tag `partial/2b-offorigin-sonnet-2026-08-18` is impl-lane input
   (unreviewed): verify against this list, log "inherited, verified" or fix.
2. **FFYR** — `FaithfulnessForcesYR/CompositionFaithfulness.lean` (file's own
   verdict C = DEGENERATE/NO at L59 vs trunk "Tier 2: Framework theorem");
   `FFYR/SelfModelDeficitFaithfulness.lean:115,140`
   (`visibleSpectrum := []`, `closure288Holds := ∃z, z = −288`).
3. **YukawaHierarchy/Bundle/*** — SpectralAction header L46 "Tier 1 conclusion
   y_c/y_τ = 3/16" vs body "identity"; ChernSimons `cs_value` always `rfl`;
   HeatKernelExpansion `trace4 = trace6 := 0`; Pontryagin `c2.value := charge`.
4. **Eta / EtaJ / IndexJ** — `Eta/IntegerCounts.lean:167` "APS axiom" `⟨2, rfl⟩`;
   `EtaJSelfConj/EtaInvariant.lean:118–120` η-sum `:= A − A`;
   `IndexJSelfConj/JSelfConjBlock.lean:163` `8 = 8`.
5. **Algebra/Forcing + Conjectures/Hodge + Algebra/CirculantMatrix** —
   `forcing_contains_octonions : True`; `voisin_… : True`; CirculantMatrix
   docstring "K = 2/3" over 2 `sorry` (Koide, flagged 06-27).

## Positive control

For any site suspected UNSOUND (not merely a shell), write a hostile file in
`output/hostile/` with `#print axioms`, record BEFORE/AFTER. Shells need no
hostile file (class is read from the term). Pre-name re-assertion points:
after each directory commit; before the manifest; before the final build.

## Pre-name re-assertion points

1. After each directory-group commit (OffOrigin → FFYR → YukawaHierarchy/Bundle
   → Eta/EtaJ/IndexJ → Algebra/Forcing+Hodge+CirculantMatrix).
2. Before writing `DECL-CLASS-MANIFEST-2b.json`.
3. Before the final `lake build SpectralPhysics`.

## G2 / G5 / G6 (frozen at seal time)

- **G2:** hopeful outcome is "everything RELABELLED". First check per file: any
  axiom universally quantified over a free structure (U1/U2/U7/U8/U9 shape) —
  if so, write the hostile file first.
- **G5:** no site ends "closed"; classes are the verdicts.
- **G6:** hostile files carry `#print axioms`; a silent compile is not evidence.
