# REPORT — Lean cleanup lane A (2026-09-06)

Branch: `lean-cleanup-A-2026-09-06` (worktree `lean-wt-A`). Not merged to `main`.

`lake build` on the tree that includes the 6-vertex certificate:

```
✔ [3359/3360] Built SpectralPhysics (3.1s)
Build completed successfully (3360 jobs).
```

Command: `lake build` (exit 0). Job count **3360**.

08896a0 touches no theorems (scripts only). Theorems below are those added/rewritten in `2b72782`, the SMDU 288 sandwich, the hostile test, and the 6-vertex certificate.

---

## 1. SMDU axiom deletion — DONE

**Commit:** `2b7278233861678ba123df9c672bacf804f3d649`
(`fix(smdu): delete IsPhysicalSpectrum/Bekenstein/Naturality axioms — 288 is the named sandwich, not a shell`)

Deleted `axiom IsPhysicalSpectrum`, `axiom BekensteinInformationBound`, `axiom NaturalityCoherence`. No replacement axiom. H4 is the `def CapacityPosit288`, not an axiom.

Command: `git show --stat 2b72782`

```
 README.md                                          |   4 +-
 SpectralPhysics.lean                               |  10 +-
 .../CapacityBound.lean                             | 180 ++++-----------------
 .../MellinFunctionalDet.lean                       |  79 +++------
 .../NaturalityBound.lean                           | 158 +++---------------
 .../PhysicalSpectrum.lean                          | 124 ++++++++------
 .../PredicateInventory.lean                        | 105 ++++--------
 .../SelfModelDeficitUnconditional/STATUS.md        | 178 +++++---------------
 .../UnconditionalGoal.lean                         | 179 ++++++++------------
 .../SelfModelDeficitUnconditional/Verdict.lean     | 178 +++++++-------------
 lakefile.lean                                      |   6 +
 test/SMDUHostile.lean                              |  86 ++++++++++
 12 files changed, 439 insertions(+), 848 deletions(-)
```

`#print axioms` (command: `lake env lean /tmp/smdu_axioms.lean`):

```
'SpectralPhysics.SelfModelDeficitUnconditional.PhysicalSpectrum.witnessSpectrum_content' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.PhysicalSpectrum.witnessSpectrum_CapacityPosit288' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.PhysicalSpectrum.counterexampleSpectrum_content' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.PhysicalSpectrum.counterexampleSpectrum_not_CapacityPosit288' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.MellinFunctionalDet.mellinRegularization_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.MellinFunctionalDet.negZetaPrimeAtZero_witnesses_mellinRegularization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.PhysicalSpectrum.CapacityPosit288' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`lake build` job count: **3360**.

---

## 2. Named-hypothesis restatement of the 288 theorems — DONE

**Commit:** `2b7278233861678ba123df9c672bacf804f3d649` (same as item 1)

`_unconditional*` renamed to `_conditional*`. Type is the existing sandwich:

```
CompletenessAtLevel2 S (negZetaPrimeAtZero V) →
SectorFaithfulNoDeadWeight S (negZetaPrimeAtZero V) →
negZetaPrimeAtZero V = 288
```

Those two named hypotheses remain open (not discharged). They are binders, not axioms. `#print axioms` is kernel-only except the three combinatorial `decide` facts, which depend on **no** axioms.

Command: `lake env lean /tmp/smdu_axioms.lean`

```
'SpectralPhysics.SelfModelDeficitUnconditional.UnconditionalGoal.self_model_deficit_conditional_param' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.UnconditionalGoal.self_model_deficit_conditional_explicit_param' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.UnconditionalGoal.self_model_deficit_conditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.UnconditionalGoal.self_model_deficit_conditional_explicit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.Verdict.v092_partial_verdict_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.Verdict.V092PartialVerdict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitRigorous.Theorem.self_model_deficit_theorem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitRigorous.Theorem.self_model_deficit_theorem_explicit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitRigorous.Theorem.self_model_deficit_theorem_288' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitRigorous.Theorem.spectralPhysicsSectoredAlgebra_dimHid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.Verdict.hidden_sector_dim_unconditional' does not depend on any axioms
'SpectralPhysics.SelfModelDeficitUnconditional.PredicateInventory.hidden_sector_unconditional' does not depend on any axioms
'SpectralPhysics.SelfModelDeficitUnconditional.PredicateInventory.axiom3_level2_unfold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitRigorous.Theorem.spectralPhysics_dim_hid_eq_288' does not depend on any axioms
```

Named hypotheses carried by the sandwich (in the type, not in the axiom list): `CompletenessAtLevel2`, `SectorFaithfulNoDeadWeight`. `CapacityPosit288` is a `def`, not used as a theorem hypothesis concluding 288.

`lake build` job count: **3360**.

---

## 3. STATUS.md / README / PredicateInventory docstring fixes — DONE

**Commit:** `2b7278233861678ba123df9c672bacf804f3d649` (same as item 1)

Command: `git show --stat 2b72782 -- README.md SpectralPhysics/SelfModelDeficitUnconditional/STATUS.md SpectralPhysics/SelfModelDeficitUnconditional/PredicateInventory.lean`

```
 README.md                                          |   4 +-
 .../PredicateInventory.lean                        | 105 ++++--------
 .../SelfModelDeficitUnconditional/STATUS.md        | 178 +++++----------------
 3 files changed, 73 insertions(+), 214 deletions(-)
```

README now lists `self_model_deficit_conditional` (sandwich) and records that `_unconditional` / `IsPhysicalSpectrum` were shells, retired 2026-09-06. STATUS.md retitled “Conditional Sandwich” and documents the three axiom deletions. PredicateInventory table marks `CompletenessAtLevel2` and `SectorFaithfulNoDeadWeight` as **open named hypotheses**.

No theorems unique to this item beyond those in items 1–2. `#print axioms` for `axiom3_level2_unfold` and `hidden_sector_unconditional` is in item 2.

`lake build` job count: **3360**.

---

## 4. Hostile test `test/SMDUHostile.lean` — DONE

**Commit:** `2b7278233861678ba123df9c672bacf804f3d649` (same as item 1; `lakefile.lean` adds `lean_lib SMDUHostile` to the default target)

`y = 1` spectrum is a `VisibleSpectrum` with `informationContent = 0`. Completeness holds (`0 ≤ 288`); sector-faithfulness fails (`288 ≤ 0`); `CapacityPosit288` fails. 288 does not follow.

Command: `lake env lean test/SMDUHostile.lean`

```
'SpectralPhysics.SelfModelDeficitUnconditional.UnconditionalGoal.self_model_deficit_conditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.UnconditionalGoal.self_model_deficit_conditional_explicit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.UnconditionalGoal.self_model_deficit_conditional_param' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.UnconditionalGoal.self_model_deficit_conditional_explicit_param' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.Verdict.v092_partial_verdict_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.Verdict.V092PartialVerdict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitRigorous.Theorem.self_model_deficit_theorem_288' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.PhysicalSpectrum.CapacityPosit288' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.PhysicalSpectrum.witnessSpectrum_CapacityPosit288' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.SelfModelDeficitUnconditional.PhysicalSpectrum.counterexampleSpectrum_not_CapacityPosit288' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'counterexample_conclusion_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'counterexample_completeness' depends on axioms: [propext, Classical.choice, Quot.sound]
'counterexample_not_sector_faithful' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Command: `lake env lean /tmp/hostile_extra2.lean` (theorems present in `test/SMDUHostile.lean` but not in its `#print axioms` list):

```
'counterexample_negZeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'counterexample_content_ne_288' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake build` job count: **3360**.

---

## 5. `check_axioms` Pattern 10 — DONE

**Commit:** `08896a0a185d57493cbe18dd2d1ebcf35ca39d39`
(`test(axioms): Pattern 10 — opaque Prop-predicate symbols and uniquely-guarded inequalities`)

No theorems in this commit. Files: `scripts/check_axioms.sh`, `scripts/README.md`.

### Historical SMDU (parent of 2b72782) — Pattern 10 fires

Command:

```
mkdir -p /tmp/hist-smdu
git show 2b72782^:SpectralPhysics/SelfModelDeficitUnconditional/PhysicalSpectrum.lean > /tmp/hist-smdu/PhysicalSpectrum.lean
git show 2b72782^:SpectralPhysics/SelfModelDeficitUnconditional/CapacityBound.lean > /tmp/hist-smdu/CapacityBound.lean
git show 2b72782^:SpectralPhysics/SelfModelDeficitUnconditional/NaturalityBound.lean > /tmp/hist-smdu/NaturalityBound.lean
git show 2b72782^:SpectralPhysics/SelfModelDeficitUnconditional/UnconditionalGoal.lean > /tmp/hist-smdu/UnconditionalGoal.lean
git show 2b72782^:SpectralPhysics/SelfModelDeficitUnconditional/Verdict.lean > /tmp/hist-smdu/Verdict.lean
bash scripts/check_axioms.sh /tmp/hist-smdu
```

Pattern 10 section of that run:

```
=== Pattern 10: opaque Prop-predicate symbols + axioms they uniquely guard ===
  (Added 2026-09-06 after SMDU IsPhysicalSpectrum shells.)
  10a: axiom whose type is `Prop` or ends in `→ Prop` / `-> Prop`
       (undefined predicate *symbol*, not a stated proposition).
  10b: axiom whose only Prop-hypotheses are applications of 10a names
       (binders `(h : Pred …)` or implication antecedents `Pred … →`).
  9-gap: 10b with a structure-typed binder and an (in)equality conclusion
       — Pattern 9 misses this because the `(h… : …)` binder exists.
  REVIEW each: a 10a symbol with no intro rule plus a 10b/9-gap axiom is
  a hypothesis=conclusion shell under the model Pred x := (conclusion).
  -- 10a opaque predicate symbols --
  /tmp/hist-smdu/PhysicalSpectrum.lean:54  axiom IsPhysicalSpectrum : VisibleSpectrum → Prop

  -- 10b axioms whose only Prop-hyps are 10a predicates --
  /tmp/hist-smdu/CapacityBound.lean:125  axiom BekensteinInformationBound (V : VisibleSpectrum) (h_phys : PhysicalSpectrum.IsPhysicalSpectrum V) : negZetaPrimeAtZero V ≤ (spectralPhysicsSectoredAlgebra.dimHid : ℝ)
  /tmp/hist-smdu/NaturalityBound.lean:124  axiom NaturalityCoherence (V : VisibleSpectrum) (h_phys : PhysicalSpectrum.IsPhysicalSpectrum V) : (spectralPhysicsSectoredAlgebra.dimHid : ℝ) ≤ negZetaPrimeAtZero V

  -- Pattern 9 gap (structure binder + inequality, guarded only by 10a) --
  /tmp/hist-smdu/CapacityBound.lean:125  axiom BekensteinInformationBound (V : VisibleSpectrum) (h_phys : PhysicalSpectrum.IsPhysicalSpectrum V) : negZetaPrimeAtZero V ≤ (spectralPhysicsSectoredAlgebra.dimHid : ℝ)
  /tmp/hist-smdu/NaturalityBound.lean:124  axiom NaturalityCoherence (V : VisibleSpectrum) (h_phys : PhysicalSpectrum.IsPhysicalSpectrum V) : (spectralPhysicsSectoredAlgebra.dimHid : ℝ) ≤ negZetaPrimeAtZero V

  Pattern 10 counts: 10a=1  10b=2  9-gap=2
```

### Live tree — SMDU gone; FaithfulnessSaturation still flagged

Command: `bash scripts/check_axioms.sh`

```
=== Pattern 10: opaque Prop-predicate symbols + axioms they uniquely guard ===
  (Added 2026-09-06 after SMDU IsPhysicalSpectrum shells.)
  10a: axiom whose type is `Prop` or ends in `→ Prop` / `-> Prop`
       (undefined predicate *symbol*, not a stated proposition).
  10b: axiom whose only Prop-hypotheses are applications of 10a names
       (binders `(h : Pred …)` or implication antecedents `Pred … →`).
  9-gap: 10b with a structure-typed binder and an (in)equality conclusion
       — Pattern 9 misses this because the `(h… : …)` binder exists.
  REVIEW each: a 10a symbol with no intro rule plus a 10b/9-gap axiom is
  a hypothesis=conclusion shell under the model Pred x := (conclusion).
  -- 10a opaque predicate symbols --
  ./SpectralPhysics/SelfModelDeficitRigorous/FaithfulnessSaturation.lean:299  axiom IsSelfModeledChannel : CirculantChannel → Prop

  -- 10b axioms whose only Prop-hyps are 10a predicates --
  ./SpectralPhysics/SelfModelDeficitRigorous/FaithfulnessSaturation.lean:316  axiom naturalityNoDeadWeight (ch : CirculantChannel) : IsSelfModeledChannel ch → carrierNorm ch ≤ breakingNorm ch

  -- Pattern 9 gap (structure binder + inequality, guarded only by 10a) --
  ./SpectralPhysics/SelfModelDeficitRigorous/FaithfulnessSaturation.lean:316  axiom naturalityNoDeadWeight (ch : CirculantChannel) : IsSelfModeledChannel ch → carrierNorm ch ≤ breakingNorm ch

  Pattern 10 counts: 10a=1  10b=1  9-gap=1
```

That live hit is **out of lane A scope** (human-judge axiom at FaithfulnessSaturation). Lane A deleted the SMDU shells Pattern 10 was written to catch.

`lake build` job count: **3360**.

---

## 6. P4 plan commit — DONE

**Commit:** `fcf5807af1bee3475ec0d8fd59cb890e1f92bceb`
(`docs(plan): P4 obligations from 2026-08-26 keystone pass`)

Command: `git show --stat fcf5807`

```
 results/REMEDIATION-PLAN.md | 26 ++++++++++++++++++++++++++
 1 file changed, 26 insertions(+)
```

No theorems. No `#print axioms`. `lake build` job count: **3360**.

---

## 7. 6-vertex Laplacian power-trace pair — DONE

**Commit:** this report commit (`docs(lean): REPORT lane A — SMDU shell removal + Pattern 10 verified`).

Stash `lane-A in-progress 6-vertex pair` used `native_decide` on `sixLapA.charpoly = sixLapB.charpoly` and failed (`charpoly` is noncomputable). Replaced by a computable Newton–Girard certificate: equal traces of `Aᵏ` and `Bᵏ` for `k = 1..6` over `Matrix (Fin 6) (Fin 6) ℤ`, each discharged by kernel `decide`, **outside** the file's `noncomputable section`. Does not invoke `charpoly`. Does not decide reconstruction / gauge. Renamed 2026-09-08 from `six_vertex_laplacian_cospectral` to `six_vertex_laplacian_power_traces_eq` because the theorem proves six power-trace equalities only; the Newton–Girard step to equal charpoly / cospectrality is not formalised.

Command: `lake env lean SpectralPhysics/Examples/SelfModelVacuity.lean` (exit 0)

```
'SelfModelVacuity.triangle_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound]
'SelfModelVacuity.triangle_spectrallyFaithful' depends on axioms: [propext, Classical.choice, Quot.sound]
'SelfModelVacuity.triangle_reconstruct' depends on axioms: [propext, Classical.choice, Quot.sound]
'SelfModelVacuity.wTriangle_path_cospectral' depends on axioms: [propext, Classical.choice, Quot.sound]
'SelfModelVacuity.not_zetaFaithful_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'SelfModelVacuity.pair_spectrallyFaithful' depends on axioms: [propext, Classical.choice, Quot.sound]
'SelfModelVacuity.pair_selfModel_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'SelfModelVacuity.pair_relSpec_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'SelfModelVacuity.six_vertex_laplacian_power_traces_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake build` (includes this file):

```
ℹ [3358/3360] Built SpectralPhysics.Examples.SelfModelVacuity (21s)
...
info: SpectralPhysics/Examples/SelfModelVacuity.lean:336:0: 'SelfModelVacuity.six_vertex_laplacian_power_traces_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
✔ [3359/3360] Built SpectralPhysics (3.1s)
Build completed successfully (3360 jobs).
```

Job count: **3360**.

---

## Summary

| Item | Status | Commit |
|---|---|---|
| SMDU axiom deletion | DONE | `2b72782` |
| Named-hypothesis restatement of the 288 theorems | DONE | `2b72782` |
| STATUS.md / README / PredicateInventory docstrings | DONE | `2b72782` |
| Hostile test `test/SMDUHostile.lean` | DONE | `2b72782` |
| `check_axioms` Pattern 10 | DONE | `08896a0` |
| P4 plan | DONE | `fcf5807` |
| 6-vertex pair | DONE | this report commit |

`lake build`: **3360 jobs**, exit 0. Not merged.
