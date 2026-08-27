# TRUNK-EDITS-2b — proposed retags (NOT applied)

Spec `lean-content-repair-2b` Task 1 deliverable. Repo boundary: Lean-only edits;
manuscript / monograph retags below are for human fold-in. First-run TRUNK-EDITS
row 4 already covers trunk L10611 FFYR — reinforced here after the 2b RELABEL.

| # | locus | current tag / text | cited Lean → class | proposed retag |
|---|---|---|---|---|
| 1 | trunk `spectral-physics.tex` L10611 | `[Tier 2: Framework theorem; Lean: FaithfulnessForcesYR/CompositionFaithfulness.lean]` | Reading C DEGENERATE/NO; supporting decls ARITHMETIC/SHELL (2b RELABELLED) | `[Tier 2: Framework claim; Lean FFYR/CompositionFaithfulness records Reading C = DEGENERATE/NO — composition does not force y_R; not a proved composition theorem]` (same intent as first-run row 4; apply once) |
| 2 | trunk L6570 / L6645 / L7513–7521 / L11088 (FFYR inventory cites) | Lean path listed as positive infrastructure | same DEGENERATE/NO file | Retarget prose to "honest negative / DEGENERATE Reading C–E" rather than "framework theorem supporting product structure" |
| 3 | trunk L6330–6332 | `YukawaHierarchy/Bundle/HeatKernelExpansion.lean`: "bundle-curvature contributions to a₄, used in the Yukawa-hierarchy derivation" | `smFinData.trace4=trace6:=0` SHELL; bridges DEFINITIONAL/ARITHMETIC | "Lean Bundle/HeatKernelExpansion carries finite-dim coefficient rewrites; `trace4`/`trace6` are zero placeholders — does not derive the Yukawa hierarchy" |
| 4 | v7 monograph `thm:charm-tau` (~L3371 in `yukawa/spectral arithmetic monograph v7.tex`) | Numerical 0.11% prediction `r_c/r_τ = 3/16`; remark already says rigorous derivation not established | Bundle `SpectralAction` / `ChernSimons` / `Pontryagin` DEFINITIONAL/ARITHMETIC identities + open `BridgeConjecture` | If/when a Lean Bundle tag is added: `[Lean: Bundle/* certifies only the cross-multiplicative identity under a matching hypothesis — not a derivation of 3/16]`. Monograph remark already honest; do not upgrade via Lean cite. |
| 5 | v0.9 / v1.0 integer headlines for Δη ∈ {12,144,168,768} (Eta/IntegerCounts lineage; locate by `Δη` / `etaJump` / APS doubling) | Tier-1 / closed integer tone where present | `aps_bismut_freed_majorana_doubling` ARITHMETIC/SHELL `⟨2,rfl⟩`; conditional jump defs | `[Lean: IntegerCounts records a trivial APS-factor witness ⟨2,rfl⟩ and conditional card arithmetic — not an APS index theorem]` |
| 6 | v0.9 / directed-side η headlines ("η + sf delivers 8" / "η=0 at J-self-conj") | positive or DEGENERATE mixed | `EtaInvariant.etaSum := A−A` DEFINITIONAL; Verdict already DEGENERATE | Keep DEGENERATE; do not cite `etaSum_eq_zero` as a computed physical η |
| 7 | v0.9 IndexJ / Clifford-8 / τ⁸ exponent headlines | Lawson–Michelsohn I.4.3 as Lean-backed | `dim_Cl06_irrep_eq_eight : 8=8` ARITHMETIC/SHELL | `[Lean: JSelfConjBlock has only the tautology 8=8; Clifford irrep dim not formalized]` |
| 8 | trunk L2420 Forcing octonions | already honest per first-run TRUNK-EDITS | `forcing_contains_octonions : True` SHELL | leave (no change) |
| 9 | Conjectures/Hodge / Voisin | conjecture framing | `voisin_… : True` SHELL | leave under Conjectures/; no trunk Tier-1 tag to strip |
| 10 | Koide / CirculantMatrix (flagged 06-27) | any "K=2/3 proved" tone | two `sorry` LEFT-OPEN | `[Lean: CirculantMatrix Koide identity is sorry — do not cite K=2/3 as machine-checked]` |

## Review-lane addendum (2026-08-18) — loci actually located

Criterion 3 asks for the monograph / v0.9 citations **located by grep**. The impl
rows 5–7 named search strategies rather than loci. The review lane ran the greps
over every `*.tex` outside `lean/`. Results, including the honest negatives:

### Verified real loci (quoted)

| # | locus | verbatim | cited Lean → class | proposed retag |
|---|---|---|---|---|
| R1 | `spectral-physics.tex:10611` | `\textsc{[Tier 2: Framework theorem; Lean: \texttt{FaithfulnessForcesYR/CompositionFaithfulness.lean}]}` | Reading C DEGENERATE/NO; decls ARITHMETIC/SHELL | as impl row 1 — **confirmed verbatim** |
| R2 | `spectral-physics.tex:6330–6332`; `spectral_physics/spectral-physics-v1.0-flat.tex:6350`; `spectral_physics/v1.0/parts/part-III-projections/01-geometry.tex:726` | "`Bundle/HeatKernelExpansion.lean`: bundle-curvature contributions to $a_4$, used in the Yukawa-hierarchy derivation" | `smFinData.trace4 = trace6 := 0` SHELL | as impl row 3 — **confirmed, and it appears in three files, not one** |
| R3 | `yukawa/spectral arithmetic monograph v7.tex:3372` (`\label{thm:charm-tau}`; numeric claim at :3388, "genuine prediction" at :3787) | `$r_c/r_\tau = 3/16$`, error 0.11% | Bundle identities DEFINITIONAL/ARITHMETIC + open `BridgeConjecture` | as impl row 4 — **confirmed** (impl's "~L3371" is the `\label`, at 3372) |
| R4 | `spectral-physics.tex:13348–13350`; `spectral_physics/spectral-physics-v1.0-flat.tex:12057`; `spectral_physics/v1.0/parts/part-IV-particle-physics/04-mixing.tex:485` | "`SpectralPhysics/Algebra/CirculantMatrix.lean` — generic circulant-matrix eigenvalue theory **used in the Koide proof**" | `koide_from_circulant` is `sorry` (`#print axioms` → `sorryAx`) | **"used in the Koide proof" → "supporting the Koide *open obligation*; `koide_from_circulant` is `sorry`"**. This is a *new* row the impl's row 10 gestured at but never located. |
| R5 | `spectral-physics.tex:29141`; `spectral_physics/v1.0/parts/part-IX-empirical/02-census.tex:392` | "`Algebra/Forcing.lean`: **Tier 1** algebraic forcing (in progress…)" | `forcing_contains_octonions : (∀ n<8, True) → (∀ n, 16≤n → True) → True` SHELL | **"Tier 1 algebraic forcing" → "algebraic forcing: Hurwitz/CayleyDickson content is Tier 1; the `Forcing.lean` assembly decl is a `True` shell"**. **New row** — impl row 8 checked only trunk L2420 and concluded "leave (no change)"; L2420 *is* honest, but this census row is not. |
| R6 | `spectral-physics.tex:3075–3077` | "`Algebra/Forcing.lean`: Parts I–II of the forcing theorem (necessity + termination)" | Parts I–II have real terms; the Part-IV assembly is the `True` shell | soft retag: name which decl carries Parts I–II, and say the assembly decl is a shell. **New row.** |

### Honest negatives — no citation exists to retag

Greps over all `*.tex` outside `lean/` return **zero** files for
`IntegerCounts`, `EtaInvariant`, `JSelfConjBlock`, `Conjectures/Hodge`,
`Bundle/SpectralAction`, `Bundle/ChernSimons`, `Bundle/Pontryagin`,
`SpectralActionConcrete`.

Therefore impl rows **5, 6, 7** (v0.9 Δη ∈ {12,144,168,768} headlines, v0.9 η
headlines, v0.9 Clifford-8 / τ⁸ headlines) **have no locus**: `spectral-physics-v0.9.2.tex`
contains no cite of any of these Lean files, and its `144` occurrences (L7747, 7774–7857,
7886–7892) are the *hidden-sector state count* (288 = 2×144 under J-pairing), an unrelated
integer. Those rows are downgraded from "proposed retag" to **NO-LOCUS**: the retag text
stays on file for whenever such a cite is first written, but nothing in the current
manuscript corpus needs it. Row 9 (Hodge/Voisin) is likewise NO-LOCUS, consistent with
the impl's "leave" verdict but for the stronger reason.

Trunk `spectral-physics.tex:2420` and `:32178` were re-read and **are** already honest
("Not formalized in Lean…"; "a content-free stub") — impl row 8's "leave" is confirmed
for those two lines specifically.

## Not applied

No edits to `spectral-physics.tex` or the v7 monograph in this run.
