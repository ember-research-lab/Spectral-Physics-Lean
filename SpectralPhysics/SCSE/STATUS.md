# `SCSE` — STATUS (void-dichotomy split)

**Scope.** The void-dichotomy upgrade of the `HeatDeathForbidden` axiom block
(`VoidDichotomy.lean`, edits to `HeatDeathForbidden.lean`; spec
`heatdeath-axiom-upgrade.tex`, source of truth `void-dichotomy-insert.tex`,
session 2026-07-04/05; branch `feature/heatdeath-split`).

**What changed.** The previously asserted axiom
`SCSE.HeatDeathForbidden.I_star` (+ `I_star_pos`, manuscript
`spectral-physics.tex` ~line 7781, exit-stability context) conflated three
claims of different epistemic ceiling. It is now carried as:

* **Part A** — dynamical no-annihilation: theorems (`VoidDichotomy.lean`).
* **Part B** — small-solution exclusion (theorem) + the dichotomy
  `Sol ⊆ {∅, k*}` (conditional on the forcing chain, cited not re-proved).
* **Part C** — the located meta-residue: exactly one documented permanent
  assumption, `axiom instantiation_nonempty` (`HeatDeathForbidden.lean`).
  Tarski meta-residue — intentionally permanent. Not a sorry. Not a TODO.
* `I_star` itself is now a `def` pinned to the manuscript's derived value
  `(e + 2)·exp(−e/(e+2)) ≈ 2.6520` (`thm:Istar-spectral`, eq:Istar);
  `I_star_pos` is a theorem.

Axiom count in this directory: **−3 / +1** (removed `I_star`, `I_star_pos`,
`RelationalKernel_nonempty`; added `instantiation_nonempty`;
`RelationalKernel_nonempty` survives as a corollary of the residue).

## Build wiring

| File | In root build? | Sorries |
|---|---|---|
| `VoidDichotomy.lean` | YES | 0 |
| `HeatDeathForbidden.lean` (edited) | YES | 0 |

## Ledger — Part A (`VoidDichotomy.lean`)

Tier: finite-dimensional linear algebra + real analysis — **T1** where CLOSED.
`#print axioms` emitted at compile time (transcript below): every CLOSED
result depends on exactly `[propext, Classical.choice, Quot.sound]`.

| Result | Verdict | Statement |
|---|---|---|
| `heat_exp_mul_exp_neg` | CLOSED | `exp (τ•L) * exp (-(τ•L)) = 1` — `Matrix.exp_add_of_commute` on the commuting pair, no self-adjointness |
| `heat_isUnit` / `thm_no_annihilation_i` | CLOSED | `IsUnit (exp (-(τ•L)))` for every finite `τ`; self-adjoint version stated on top |
| `thm_no_annihilation_ii` | CLOSED (diagonalized basis) | normalized heat weight of every mode → ground indicator / ground multiplicity as `τ → ∞` |
| `normalized_heat_tendsto_groundProjector` | CLOSED (diagonal Laplacians) | matrix form: `exp(-(τL))/Tr exp(-(τL)) → P₀ / rk P₀` entrywise, `L = diagonal μ` |
| `one_le_groundMult` / `one_le_groundProjector_rank` | CLOSED | ground projection has rank ≥ 1 — the ground state is a state |
| `groundProjector_mul_self`, `groundProjector_rank` | CLOSED (supporting) | `P₀` idempotent; `rk P₀ = groundMult` |
| `heat_death_forbidden` (old name, now a theorem) | CLOSED | forbidden **as annihilation** (units at all finite `τ`), permitted **as asymptotics** (`rk P₀ ≥ 1`) |
| General self-adjoint `L` form of (ii) | **CONDITIONAL** — named gap | conjugating the diagonal-basis limit through the eigenbasis (`Matrix.IsHermitian.spectral_theorem`) is not formalized; spec explicitly allows PARTIAL with (i) closed |

## Ledger — Part B (`VoidDichotomy.lean`)

| Result | Verdict | Statement |
|---|---|---|
| `ignitionDatum` (+ `ignitionDatum_isSome_iff`) | CLOSED | ignition datum as a **partial** function (`Option`): pair of distinct spectral levels, `none` unless `1 < card` |
| `prop_small_exclusion` | CLOSED | `card ≤ 1 ⇒ ignitionDatum = none` — fails at the *existence* step, not vacuously; closes the insert's Open Problem syntactically |
| `prop_small_exclusion_dim` | CLOSED | dimension-indexed: `N ≤ 1` (void and point) ⇒ no ignition datum |
| executable checks | CLOSED | `example`s at N = 0, 1 (`none`, by `decide`) and the 2-level toy (`isSome`, value `(0, 3)`); 3-mode triad-shape check; concrete 3×3 triangle-Laplacian heat unit |
| `prop_dichotomy` | **CONDITIONAL (T2) — by design** | `Sol ⊆ {void, k*}` given (1) nonvoid solutions have a defined ignition datum, (2) the manuscript forcing chain (Cayley–Dickson/Hurwitz, 3×128 count, gauge+chirality closures) as a **hypothesis** — cited, not re-proved, per the insert's Lean-upgrade section |

## Ledger — Part C + rewire (`HeatDeathForbidden.lean`)

| Item | Verdict |
|---|---|
| `instantiation_nonempty` | **PERMANENT ASSUMPTION (documented)** — the single remaining assumption where the axiom block was; the instantiation of the nonempty branch is not an internal predicate (Tarski). Not OPEN: intentionally permanent. Counted in the underivable inventory (units morphism + orientation ℤ/2 + instantiation bit). |
| `RelationalKernel_nonempty` | CLOSED as corollary — depends on exactly `[instantiation_nonempty]` |
| `I_star` (def) / `I_star_pos` | CLOSED — value pinned to manuscript eq:Istar; positivity a theorem, axioms-clean |
| old axiom entry (`axiom I_star`) | **moved to CLOSED (Parts A, B) + the one documented permanent assumption (Part C)** |

## Downstream rewire report

Downstream users of this namespace (`SelfRef/SpectralFloor`,
`SCSE/DegeneracyBreaking`, `SCSE/SelfAlignedEvolution`,
`DarkMatter/ZeroedModes`, `MetaPattern/PositivityGapLocalization`) never
consumed `I_star` except through `SelfReferenceClosure`, whose definition is
unchanged (`I_star < integratedInformation k`; `I_star` is now a def). **No
downstream statement was changed or weakened; all compile unchanged.** Their
kernel-valued opaques give them a dependence on the (renamed) nonemptiness
assumption exactly as before — now the single documented
`instantiation_nonempty` instead of the undocumented
`RelationalKernel_nonempty`.

Out of scope, unchanged, and still axioms (pre-existing Phase-2.1/3
scaffolding, honestly listed): `lambda_1_pos_from_self_reference` (T2),
`lambda_floor_exists` (T3), `scse_preserves_self_reference` (T2),
`de_sitter_asymptote_from_positive_lambda` (T1 cited),
`lambda_cc_eq_lambda_1_limit` (placeholder). The dated sweep
`results/AXIOM-SOUNDNESS-SWEEP.md` still lists the pre-split axiom names —
it is a point-in-time record, superseded here.

## `#print axioms` transcript (compile-time, 2026-07-06 build)

```
'…VoidDichotomy.thm_no_annihilation_i'  depends on axioms: [propext, Classical.choice, Quot.sound]
'…VoidDichotomy.thm_no_annihilation_ii' depends on axioms: [propext, Classical.choice, Quot.sound]
'…VoidDichotomy.normalized_heat_tendsto_groundProjector' depends on axioms: [propext, Classical.choice, Quot.sound]
'…VoidDichotomy.one_le_groundProjector_rank' depends on axioms: [propext, Classical.choice, Quot.sound]
'…VoidDichotomy.heat_death_forbidden'   depends on axioms: [propext, Classical.choice, Quot.sound]
'…VoidDichotomy.prop_small_exclusion'   depends on axioms: [propext, Classical.choice, Quot.sound]
'…VoidDichotomy.prop_small_exclusion_dim' depends on axioms: [propext, Classical.choice, Quot.sound]
'…VoidDichotomy.prop_dichotomy'         depends on axioms: [propext, Classical.choice, Quot.sound]
'…HeatDeathForbidden.I_star_pos'        depends on axioms: [propext, Classical.choice, Quot.sound]
'…HeatDeathForbidden.RelationalKernel_nonempty' depends on axioms: [instantiation_nonempty]
'…HeatDeathForbidden.heat_death_forbidden_conditional' depends on axioms:
    [propext, Classical.choice, Quot.sound, instantiation_nonempty,
     lambda_floor_exists, scse_preserves_self_reference]
```

No new axioms beyond the single documented `instantiation_nonempty`.
Full `lake build`: green, 3339 jobs, all existing targets included.
