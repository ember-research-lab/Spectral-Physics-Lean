# REPORT — Lean cleanup lane B (2026-09-06)

**Worktree:** `/home/aaron/spectral-physics-manuscript/lean-wt-B`
**Branch:** `lean-cleanup-B-2026-09-06`
**Date:** 2026-09-07
**Scope of this lane:** rows U1, U4, U5, U7, U8, U9.
**Explicitly out of this lane:** row **U2** (`KasparovProductUniqueness` axioms K1/K2/K3) is **NOT DONE** in this lane. A prior commit `1ee37aa` on the branch is not this lane's deliverable and is not claimed here.

**`lake build` (this session, after U4/U5/U7 commits):**

```
Build completed successfully (3358 jobs).
```

Job count **3358** is used for every row below. Hostile files are not Lake library members; they were compiled with `lake env lean hostile/<file>.lean`.

No row is claimed without the pasted command output that supports it.

---

## U1 — KSR ⊥-topology instance

**Status:** DONE
**Commit:** `fb15e7fc282ef8fd34cb87e9dcc574f68fab9c93`
(`fix(U1): remove KSR ⊥ topology instance — compactness is a named hypothesis`)

Global `instance : TopologicalSpace KSR := ⊥` removed. Theorems take `[TopologicalSpace KSR]`; compactness is an explicit hypothesis. The old compactness axiom `rellich_kondrachov_trace_class` is already gone (2026-08-18).

### Hostile-before (`lake env lean hostile/U1-KSRFalse.lean`)

```
hostile/U1-KSRFalse.lean:31:15: error(lean.unknownIdentifier): Unknown identifier `rellich_kondrachov_trace_class`
hostile/U1-KSRFalse.lean:30:29: error: unsolved goals
⊢ False
'ksr_false' depends on axioms: [sorryAx]
```

### `#print axioms` after (`lake env lean hostile/U1-after-print-axioms.lean`)

```
'SpectralPhysics.KSRCompactness.ksr_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpectralPhysics.KSRCompactness.ksr_subset_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpectralPhysics.KSRCompactness.ksr_compact_inter_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpectralPhysics.KSRCompactness.ksr_invariant_sobolev_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.KSRCompactness.KSR_compactness_verdict' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpectralPhysics.KSRCompactness.KSR_compactness_verdict_constructive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.BasinConnectivity.coercive_sublevels_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.BasinConnectivity.v092_G3_verdict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 morse_two_minima_disconnect,
 palais_smale_morse_basin_closure]
'SpectralPhysics.BasinConnectivity.SAGF_basin_closure_from_hypotheses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 palais_smale_morse_basin_closure]
```

Local `⊥` cannot discharge `IsCompact` of an infinite Sobolev class (see `hostile/U1-after-no-bot.out`).

### `lake build`

```
Build completed successfully (3358 jobs).
```

---

## U4 — BasinConnectivity discrete-topology falsehood

**Status:** ALREADY-FIXED
**Commit (this session, documentation + hostile):** `54a404a1e8b56a3ca3695bb06e9ac417d109438a`
(`fix(U4,U5): tag PoincareDuality Cantor-uninhabited as VACUOUS; BasinConnectivity already renamed`)

The 2026-08-18 repair renamed `BasinConnectivity` → `BasinConnectivity_superseded_conjecture` (DEMOTED relabel; the discrete-topology defect is unchanged). This lane did not alter `SpectralPhysics/BasinConnectivity/` source. The uncommitted hostile uses the old identifier and does not typecheck.

### Hostile-before (`lake env lean hostile/U4-BasinFalse.lean`)

```
hostile/U4-BasinFalse.lean:10:50: error: Function expected at
  BasinConnectivity
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  F

Hint: The identifier `BasinConnectivity` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
hostile/U4-BasinFalse.lean:26:35: error: don't know how to synthesize placeholder for argument `F`
context:
h : SAGFPalaisSmaleHypotheses
⊢ KSR → ℝ
'basinConnectivity_false' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'sagf_hyps_false' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'morse_provable' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `#print axioms` after

No dedicated U4-after file. The BasinConnectivity dependents compiled in the U1 after-file (`hostile/U1-after-print-axioms.lean`) print:

```
'SpectralPhysics.BasinConnectivity.coercive_sublevels_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.BasinConnectivity.v092_G3_verdict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 morse_two_minima_disconnect,
 palais_smale_morse_basin_closure]
'SpectralPhysics.BasinConnectivity.SAGF_basin_closure_from_hypotheses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 palais_smale_morse_basin_closure]
```

### `lake build`

```
Build completed successfully (3358 jobs).
```

---

## U5 — PoincareDuality predicate vacuity

**Status:** DONE (honest VACUOUS/SHELL demotion; predicate still uninhabited)
**Commit:** `54a404a1e8b56a3ca3695bb06e9ac417d109438a`
(`fix(U4,U5): tag PoincareDuality Cantor-uninhabited as VACUOUS; BasinConnectivity already renamed`)

`PoincareDuality T` is `Function.Bijective (T.intersectionForm)` with
`T.intersectionForm : 𝕆 → (𝕆 → 𝕆)`. This is never surjective (Cantor),
so the predicate holds for **no** `T`. Dependents were kept and marked
`-- VACUOUS:` in docstrings; they are not cited as a Dixon-specific
obstruction. The non-vacuous algebraic negative is
`not_wellDefinedOnClasses_canonical_dixon` (zeroth-order / associator).
This is SHELL, not OPEN, and not a repair of the carrier type.

### Hostile-before / current-state (`lake env lean hostile/U5-PDVacuous.lean`)

Compiles. Output:

```
'poincareDuality_never' depends on axioms: [propext, Classical.choice, Quot.sound]
'connes_PD_definition_vacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'dixon_pd_obstruction_shell' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `#print axioms` after (`lake env lean hostile/U5-after-print-axioms.lean`)

```
'SpectralPhysics.DixonPoincareDuality.connes_PD_definition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 connes_PD_definition]
'SpectralPhysics.DixonPoincareDuality.bochniak_sitarz_PD_obstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bochniak_sitarz_PD_obstruction]
'SpectralPhysics.DixonPoincareDuality.dixon_pd_obstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bochniak_sitarz_PD_obstruction]
'SpectralPhysics.DixonPoincareDuality.dixon_pd_fails_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 connes_PD_definition]
'SpectralPhysics.DixonPoincareDuality.PD_fails_for_dixon' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpectralPhysics.DixonPoincareDuality.PD_fails_for_canonical_dixon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.DixonPoincareDuality.PD_implies_zerothOrder_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.DixonPoincareDuality.not_wellDefinedOnClasses_canonical_dixon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.DixonPoincareDuality.dixon_pd_has_nonzero_associator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.DixonPoincareDuality.dixon_pd_not_wellDefined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`PD_fails_for_dixon` / `PD_fails_for_canonical_dixon` / `PD_implies_zerothOrder_canonical` are kernel-only because the PD antecedent is uninhabited (false-antecedent). `dixon_pd_obstruction` still cites `bochniak_sitarz_PD_obstruction` (named axiom; not a Dixon-specific fact). `not_wellDefinedOnClasses_canonical_dixon` is kernel-only and is the non-vacuous algebraic negative.

### `lake build`

```
Build completed successfully (3358 jobs).
```

---

## U7 — `standardModel_three_generations` ∀-axiom

**Status:** ALREADY-FIXED (library pin 2026-08-18); this session added the hostile-before that actually derives `False`
**Commits:**
- library pin documented: `66f74e6645996e55a92f8eeb3d98018c9e4448bf` (`docs(U7): verify already-fixed three-generations pin — hostile 0=3 no longer typechecks`)
- this session: `631ed5f3b5e5512c977c04ae421d72093c10287e` (`fix(U7): three generations is a hypothesis, not an axiom`)

The library identifier is already the theorem
`standardModelTriple.n_generations = 3 := rfl`, pinned to the concrete
structure field `n_generations := 3`. It is not a `∀`-axiom. This
session's new file `hostile/U7-ThreeGenFalse.lean` re-declares the
deleted `∀`-axiom locally and derives `False` from the witness
`n_generations := 0`.

### Hostile-before (`lake env lean hostile/U7-ThreeGenFalse.lean`)

Compiles. Output:

```
'u7_false' depends on axioms: [propext, standardModel_three_generations_forall]
```

No `sorryAx`. Against the *library* identifier (not the reconstructed axiom), `hostile/U7-MajoranaFalse.lean` does not typecheck:

```
hostile/U7-MajoranaFalse.lean:10:12: error: Function expected at
  standardModel_three_generations
but this term has type
  standardModelTriple.n_generations = 3

Note: Expected a function because this term is being applied to the argument
  hostile
hostile/U7-MajoranaFalse.lean:9:48: error: unsolved goals
⊢ False
'false_from_three_generations' depends on axioms: [sorryAx]
```

### `#print axioms` after (`lake env lean hostile/U7-after-witness-excluded.lean`)

```
'SpectralPhysics.MajoranaBlock.standardModel_three_generations' does not depend on any axioms
'SpectralPhysics.MajoranaBlock.HypothesisB.standardModelTriple_n_generations_eq' does not depend on any axioms
'SpectralPhysics.MajoranaBlock.HypothesisB.standardModelTriple_JSC_multiplicity_eq_six' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 connes_marcolli_2008_thm_1_214]
'SpectralPhysics.MajoranaBlock.Discriminator.standardModelTriple_JSC_multiplicity_is_six' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 connes_marcolli_2008_thm_1_214]
'SpectralPhysics.MajoranaBlock.Discriminator.framework_predicts_hypothesisB_with_multiplicity_six' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 connes_marcolli_2008_thm_1_214]
'SpectralPhysics.MajoranaBlock.Discriminator.standardModelTriple_verdict' does not depend on any axioms
```

The pin itself is axiom-free (`rfl`). JSC-multiplicity `= 6` still cites `connes_marcolli_2008_thm_1_214` (out of U7 scope: that axiom is the extended-Dirac multiplicity *rule*, not the generation count).

### `lake build`

```
Build completed successfully (3358 jobs).
```

---

## U8 — Dixon order-one / `bochniak_sitarz_zerothOrder_reduction`

**Status:** ALREADY-FIXED
**Commit:** `fd5f418bacf78e360b1f3bc7a9b7418b360ad852`
(`docs(U8): verify already-fixed Dixon order-one — axiom gone, reduction OPEN`)

The unconstrained-`D` axiom is already deleted (2026-08-18). The zero map still satisfies unconstrained `OrderOne`. Non-degeneracy of `D` was not added; order-one-for-every-`D` stays OPEN.

### Hostile-before (`lake env lean hostile/U8-DixonU8False.lean`)

```
hostile/U8-DixonU8False.lean:9:8: error: `SpectralPhysics.DixonOrderOne.zero_map_orderOne` has already been declared
hostile/U8-DixonU8False.lean:16:5: error(lean.unknownIdentifier): Unknown identifier `bochniak_sitarz_zerothOrder_reduction`
'SpectralPhysics.DixonOrderOne.u8_false' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

### `#print axioms` after (`lake env lean hostile/U8-after-print-axioms.lean`)

```
'SpectralPhysics.DixonOrderOne.zero_map_orderOne' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpectralPhysics.DixonOrderOne.dixon_reduction_hypothesis_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.DixonOrderOne.dixon_order_one_unconstrained_has_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SpectralPhysics.DixonOrderOne.dixon_has_nonzero_associator' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpectralPhysics.DixonOrderOne.dixon_LR_does_not_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `lake build`

```
Build completed successfully (3358 jobs).
```

---

## U9 — second-law axiom `second_law_entropy_increase`

**Status:** ALREADY-FIXED
**Commit:** `ad2f2f9e36623780ef0c420f8c38fea935718b04`
(`docs(U9): verify already-fixed second-law axiom deletion — entropy monotonicity OPEN`)

The axiom is already deleted (2026-08-18, zero consumers). Heat-flow content was not added: `h_heat_flow : True` cannot be repaired without semigroup/Klein infrastructure. Remaining `FourLaws` theorems are kernel-only.

### Hostile-before (`lake env lean hostile/U9-UnsoundCheck.lean`)

```
hostile/U9-UnsoundCheck.lean:24:2: error(lean.unknownIdentifier): Unknown identifier `second_law_entropy_increase`
```

### `#print axioms` after (`lake env lean hostile/U9-after-print-axioms.lean`)

```
'SpectralPhysics.Thermo.zeroth_law' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpectralPhysics.Thermo.first_law' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpectralPhysics.Thermo.first_law_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpectralPhysics.Thermo.third_law_ground_state_dominates' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpectralPhysics.Thermo.partitionFunction_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpectralPhysics.Thermo.partition_function_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpectralPhysics.Thermo.partition_excess_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `lake build`

```
Build completed successfully (3358 jobs).
```

---

## U2 — KasparovProductUniqueness K1/K2/K3

**Status:** NOT DONE in this lane.

This lane does not claim, close, or re-audit `KasparovProductUniqueness` axioms K1/K2/K3. Existing branch commit `1ee37aa` is outside this report's claimed rows.

---

## Summary

| Row | Status | Commit |
|-----|--------|--------|
| U1 | DONE | `fb15e7f` |
| U4 | ALREADY-FIXED | `54a404a` (hostile + docs; rename is 2026-08-18) |
| U5 | DONE (VACUOUS/SHELL demotion) | `54a404a` |
| U7 | ALREADY-FIXED | `66f74e6` + `631ed5f` (hostile-before) |
| U8 | ALREADY-FIXED | `fd5f418` |
| U9 | ALREADY-FIXED | `ad2f2f9` |
| U2 | **NOT DONE in this lane** | — |

Do not merge to main. This report does not claim a CI/gate verdict beyond the pasted `lake build` line above.
