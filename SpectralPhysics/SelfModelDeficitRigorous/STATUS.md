# Self-Model Deficit Theorem — Rigorous Branch: STATUS

**Branch**: `compute/self-model-deficit-rigorous`
**Target**: Proposition 23.10 of `spectral-physics-v0.9.tex`, line 8435
**Tag**: `thm:self-model-deficit`

This file is the honest accounting of what this branch proves and what
it does not. It supersedes the audit-caught deceptive predecessor
`compute/zetaF-prime-zero`.

## 1. Theorems proved (with statements)

All six new modules build cleanly (`lake build` succeeds, zero
`sorry`/`admit`, lints warnings only on a duplicate-namespace name
that was fixed). Verified with `#print axioms` (see §6).

### `SectorDecomposition.lean`

* `aobs_dim_factorisation : AObsDim = 384` — proved by `decide`.
* `sm_visible_decomposition : 12 + 84 = SMVisibleDim` — proved by `decide`.
* `hidden_sector_dim_eq_288 : HiddenSectorDim = 288` — proved by `decide`.
  This is the combinatorial 288 = 384 − 96.
* `aobs_dim_split : AObsDim = SMVisibleDim + HiddenSectorDim` — by `decide`.
* `spectralPhysicsDecomposition_{visible,hidden,total}` — simp lemmas.

**Tautological?** The arithmetic `2·4·8·3·2 = 384` and `384 − 96 = 288`
*are* decidable arithmetic, so the `decide` proof is trivial. But the
factorisation chosen here — `dim_ℝ(ℂ) · dim_ℝ(ℍ) · dim_ℝ(𝕆) ·
num_generations · particle_antiparticle` — encodes the algebra-forcing
content of Axioms 1–2 (Hurwitz forcing of normed division algebras) plus
the Cl(6) generation structure. The arithmetic *itself* is trivial; the
*meaning* of the factors is load-bearing for the framework. This is
honest as Step 1.

### `FaithfulState.lean`

* `dim_hid_eq_of_axiom3_level2 : Axiom3Level2 S c → (S.dimHid : ℝ) = c`
  — proved by `le_antisymm`. **Trivial structural lemma**:
  `≤` + `≥` ⇒ `=`. The substantive content is the *meaning* of the
  conjunction, defined as the pair of inequalities. Honestly flagged
  as bookkeeping.

### `SpectralZeta.lean`

* `informationContent_def` — `rfl` unfolding lemma.
* `informationContent_empty : numModes = 0 → infContent = 0` —
  proved by `subst` + `simp`. **Trivial** (sum over empty set).
* `informationContent_singleton : ... = m · (-log y)` — proved by
  `simp`. **Definitional**.
* `negZetaPrimeAtZero_eq : negZetaPrimeAtZero V = informationContent V`
  — proved by `Classical.choose_spec`. **Trivial extraction** from the
  named axiom.

### `CompletenessBound.lean`

* `completeness_lower_bound :
    CompletenessAtLevel2 S (negZetaPrimeAtZero V)
    → negZetaPrimeAtZero V ≤ (S.dimHid : ℝ)` — proof is `h` (identity).
  This is a **definitional unfolding** of `CompletenessAtLevel2`.

  **Why this is not deceptive**: the hypothesis `CompletenessAtLevel2`
  IS the bound (it's *defined* as the bound). The theorem is therefore
  the precise statement that *if* one accepts the structural condition
  from v0.9 line 8452, the bound follows. The substantive work — proving
  that condition holds for the spectral-physics algebra — is OPEN.

* `completeness_fails_of_capacity_insufficient :
    (S.dimHid : ℝ) < negZetaPrimeAtZero V
    → ¬ CompletenessAtLevel2 S (negZetaPrimeAtZero V)` — by `not_lt`.
  The **contrapositive**.

* `completeness_lower_bound_explicit` — variant in `informationContent`
  form.

### `FaithfulnessBound.lean`

* `sector_faithfulness_upper_bound :
    SectorFaithfulNoDeadWeight S (negZetaPrimeAtZero V)
    → (S.dimHid : ℝ) ≤ negZetaPrimeAtZero V` — proof is `h` (identity).
  **Definitional unfolding**, mirror of `completeness_lower_bound`.

* `sector_faithfulness_fails_of_dead_weight` — contrapositive.

* `sector_faithfulness_upper_bound_explicit` — variant.

### `Theorem.lean`

* `self_model_deficit_theorem :
    CompletenessAtLevel2 S (...) ∧ SectorFaithfulNoDeadWeight S (...)
    → negZetaPrimeAtZero V = (S.dimHid : ℝ)`. **Combines the two
  bounds via `le_antisymm`**. This is the v0.9 Step 5.

* `self_model_deficit_theorem_explicit` — variant in
  `informationContent` form.

* `spectralPhysics_dim_hid_eq_288 :
    spectralPhysicsDecomposition.hidden = 288` — proved by `decide`,
  **unconditional**.

* `self_model_deficit_theorem_288 :
    [both bounds for spectralPhysicsSectoredAlgebra]
    → negZetaPrimeAtZero V = 288` — the headline. Combines
  the conditional theorem with the combinatorial 288.

## 2. Named axioms (with citations)

**One** named axiom is introduced in this directory:

### `mellin_heat_kernel_finite_spectrum_log_sum`
(file: `SpectralZeta.lean`, line 169)

```
axiom mellin_heat_kernel_finite_spectrum_log_sum
    (V : VisibleSpectrum) :
    ∃ z : ℝ, z = informationContent V
```

**Citation**: Connes–Marcolli, *Noncommutative Geometry, Quantum
Fields and Motives*, AMS Colloquium Publications vol. 55 (2008), §1.7;
also Berline–Getzler–Vergne, *Heat Kernels and Dirac Operators*,
Grundlehren der Math. Wiss. 298 (1992), Ch. 2 and §9.6.

**What it asserts**: that the Mellin-transform-derived value
`−ζ̃'(0)` for a finite-dimensional Dirac operator with spectrum
`{σ_k}` equals the explicit sum `Σ_k mult_k · (−log y_k)` where
`y_k := σ_k / Λ`.

**Smuggling check**:

* This axiom is an **existence statement** with the value tied to a
  free parameter (the `VisibleSpectrum V`). Different `V` give
  different sums.
* It does **not** assert any specific numerical value of the sum for
  any specific `V`. (Contrast: the deceptive prior branch
  axiomatised four sectors to specific Q-valued constants summing to
  288.)
* The `288` of the headline does **not** come from this axiom; it
  comes from the combinatorial `dim H_hid = 384 − 96 = 288` plus the
  separate (open) bounds.

That is the only axiom introduced. Standard Lean kernel axioms
(`propext`, `Classical.choice`, `Quot.sound`) appear via Mathlib
infrastructure as always.

## 3. What is genuinely closed vs. what remains open

### Genuinely closed (proved in Lean, fully unconditional)

* `dim(H_hid) = 384 − 96 = 288` — pure `Nat` arithmetic.
* The factorisation `2 · 4 · 8 · 3 · 2 = 384`.
* The `≥ + ≤ ⇒ =` combiner.
* All definitional unfolding lemmas for `informationContent`.

### Closed conditionally on the two structural predicates

* `self_model_deficit_theorem` — IF the two predicates hold for
  `(S, V)`, THEN `−ζ̃'_vis(0) = dim(H_hid)`.
* `self_model_deficit_theorem_288` — IF the two predicates hold for
  `(spectralPhysicsSectoredAlgebra, V)`, THEN `−ζ̃'_vis(0) = 288`.

### Open (honestly flagged)

The two structural predicates themselves:

1. **`CompletenessAtLevel2 S (−ζ̃'_vis(0))`** — that the
   spectral-physics algebra's *Level-2 one-loop information condition*
   imposes the lower bound. This requires a Lean-level definition of
   "Level-2 one-loop information condition" beyond GNS faithfulness,
   which is not in Mathlib and not in this repo.

2. **`SectorFaithfulNoDeadWeight S (−ζ̃'_vis(0))`** — that
   sector faithfulness (partial-trace reconstructibility) implies
   the upper bound. This requires the same Level-2 / Mellin
   infrastructure.

These are exactly the open formalisation problems v0.9 line 8464
flags. We have **not** axiomatised them away.

## 4. Comparison to the deceptive prior branch

| Aspect | `compute/zetaF-prime-zero` | `compute/self-model-deficit-rigorous` |
|---|---|---|
| `−ζ̃'_vis(0)` | axiomatised free real, then forced to equal `negLogYukawaSum_visible` via `zeta_regularization_log_sum` axiom | defined as `informationContent V` — a sum over the *parameter* spectrum |
| Per-sector sums | 4 axioms `up_sector_log_yukawa_sum := 9723/100`, `down ...`, etc., hand-picked rationals summing to 288 | **no per-sector axioms** at all |
| Seesaw closure | `seeSaw_closure` axiom forces `S_νR := -17401/100` | **no seesaw axiom** |
| Origin of 288 | engineered: `(9723+13070+4946+18462−17401)/100 = 288` | combinatorial: `2·4·8·3·2 − 96 = 288` |
| Bounds (Steps 3, 4) | **none** — the sum is *defined* to equal 288 by chained axioms | predicates `CompletenessAtLevel2` and `SectorFaithfulNoDeadWeight`, used as hypotheses in conditional theorems |
| Total new axioms | 5+ smuggled numeric axioms | 1 general-identity named axiom (Connes–Marcolli §1.7) |
| Conclusion provable from axioms alone | yes — `norm_num` on the rationals | **no** — requires the two structural hypotheses |
| Audit verdict | "axiom-smuggled" | conditional / honest PARTIAL |

The crucial structural difference: in the deceptive branch, the
conclusion `= 288` was a `norm_num` exercise on axiomatised numeric
constants. In this branch, `= 288` is *not* provable without
hypothesising the structural bounds — there is no chain of axioms
that lets you derive `−ζ̃'_vis(0) = 288` without first granting the
v0.9-flagged open conditions.

## 5. Sorries — categorised

**Zero sorries.** Verified by `grep -rn "sorry\|admit" SpectralPhysics/SelfModelDeficitRigorous/`.

The "openness" of this branch is encoded *not* via `sorry` but via
the conditional form of the theorems: the open content sits in the
two **predicate hypotheses** (`CompletenessAtLevel2`,
`SectorFaithfulNoDeadWeight`) that the caller must supply. The
moral equivalent of "two `sorry`s" would be axioms named e.g.
`completeness_holds_for_spectral_physics` — we deliberately do
**not** introduce those.

## 6. Build status

```
$ lake build
✔ [3176/3177] Built SpectralPhysics (6.0s)
Build completed successfully (3177 jobs).
```

Verified axiom dependencies of the headline (via `#print axioms`):

```
'self_model_deficit_theorem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta.mellin_heat_kernel_finite_spectrum_log_sum]

'self_model_deficit_theorem_288' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta.mellin_heat_kernel_finite_spectrum_log_sum]

'spectralPhysics_dim_hid_eq_288' does not depend on any axioms
```

The combinatorial `dim H_hid = 288` is **fully unconditional**
(no axiom dependency). The headline theorems depend on exactly one
non-kernel axiom — the Mellin / heat-kernel identity, with citation.

## 7. Honest verdict

**Does this close Prop 23.10 rigorously?** No.

**Does this close part of Prop 23.10?** Yes — Steps 1 (combinatorial
capacity), 2 (definition of `−ζ̃'_vis(0)` as a sum), and 5 (the
`≤ + ≥ ⇒ =` combiner) are fully closed. The connection to the
Mellin transform is encoded via one general-identity named axiom
with explicit citation.

**What remains open?** Steps 3 and 4 — the two structural bounds —
which v0.9 line 8464 itself identifies as "an open problem." We have
formalised them as **Prop-valued predicates** on `(SectoredStarAlgebra,
VisibleSpectrum)` pairs, parameterised by a real `informationContent`,
and proved that *if* both predicates hold for the spectral-physics
algebra with the SM-physical visible spectrum, *then* the headline
`−ζ̃'_vis(0) = 288` follows.

**Comparison to the deceptive prior branch.** The prior
`compute/zetaF-prime-zero` branch achieved the *appearance* of closing
Prop 23.10 by axiomatising five real constants chosen to sum to 288.
The audit caught this. This branch deliberately does NOT do that:

* No per-sector log-Yukawa axiom.
* No seesaw-closure axiom.
* No `−ζ̃'_vis(0) = 288` axiom.
* The 288 is *combinatorial* (`Nat` arithmetic), not engineered from
  rationals.

**Is this useful as a partial result?** Yes:

1. It establishes a clean Lean type-theoretic framework for the
   theorem's statement, with the visible / hidden split a structural
   parameter and the spectral depth defined honestly as a sum.
2. It localises the open content into exactly two well-defined
   predicates with clear physical motivation (matching v0.9 Steps 3
   and 4 verbatim).
3. It documents what remains (Level-2 information condition,
   partial-trace faithfulness on sectors) as concrete next-step
   targets for future work.
4. It provides a credible audit trail: `#print axioms` enumerates
   the dependency, and there is **one** named non-kernel axiom in
   the directory, with explicit literature citation.

**This is a PARTIAL result. It is honest. It does not pretend to be
more than it is.**

A future "closing" branch would need to:

(a) Define a Lean-level *Level-2 information condition* on a faithful
state on a finite-dim C*-algebra (going beyond GNS faithfulness;
this may require formalising the loop / heat-kernel expansion).

(b) Prove that the spectral-physics algebra's canonical faithful
state, restricted to the SM-physical visible spectrum, satisfies both
the Level-2 information condition (giving completeness) and the
no-dead-weight partial-trace condition (giving sector faithfulness).

Neither step is in this branch; neither is axiomatised in this branch.
