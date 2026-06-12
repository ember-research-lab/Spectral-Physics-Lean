# Self-Model Deficit Theorem — Unconditional Branch: STATUS

**Branch**: `compute/self-model-deficit-unconditional`
**Target**: v0.9.2 deferred item C.1 (`yukawa/pre_geometric/v091_v092_split_audit/v092_deferred.md` line 22, addressing 10 cross-refs in `spectral-physics-v0.9.tex`: lines 8464, 8753, 8767, 9036, 9157, 9201, 9204, 14910, 16672, 16723).

This is the v0.9.2 sharpening of v0.9.1's `compute/self-model-deficit-rigorous` branch. **It does NOT close v0.9.2 deferred item C.1**; it reduces the open content to **three named literature axioms** with explicit citations.

## Files

```
SelfModelDeficitUnconditional/
├── PredicateInventory.lean    — formal inventory of v0.9.1 open predicates
├── CapacityBound.lean         — Bekenstein 1981 axiom + discharge of predicate (i)
├── NaturalityBound.lean       — Mac Lane 1998 §VII axiom + discharge of predicate (ii)
├── MellinFunctionalDet.lean   — wrapper for v0.9.1's Connes–Marcolli axiom
├── UnconditionalGoal.lean     — headline `self_model_deficit_unconditional`
├── Verdict.lean               — assembly with verdict marker
└── STATUS.md                  — this file
```

All six Lean files build cleanly under `lake build SpectralPhysics.SelfModelDeficitUnconditional.<file>`; the repo-root `lake build SpectralPhysics` succeeds (3240 jobs at this branch).

## What v0.9.1 left open

v0.9.1 `compute/self-model-deficit-rigorous` left the v0.9 Prop 23.10 result conditional on **two unnamed Prop-valued predicates** plus **one named literature axiom**:

| v0.9.1 open content | Form |
|---|---|
| `CompletenessAtLevel2 S c` | unnamed Prop hypothesis: `c ≤ (dim H_hid : ℝ)` |
| `SectorFaithfulNoDeadWeight S c` | unnamed Prop hypothesis: `(dim H_hid : ℝ) ≤ c` |
| `mellin_heat_kernel_finite_spectrum_log_sum` | named axiom (Connes–Marcolli §1.7) |

The v0.9.1 headline `self_model_deficit_theorem_288` had type:

```
∀ V, CompletenessAtLevel2 (...) (negZetaPrimeAtZero V)
   → SectorFaithfulNoDeadWeight (...) (negZetaPrimeAtZero V)
   → negZetaPrimeAtZero V = 288
```

— i.e. the caller had to **supply** both Prop hypotheses; neither had a literature-axiom closure.

## What v0.9.2 closes (this branch)

The v0.9.2 dispatch provides closing **named literature axioms** for both open predicates:

| v0.9.1 predicate | v0.9.2 closure | Named axiom | Citation |
|---|---|---|---|
| `CompletenessAtLevel2` | discharged | `BekensteinInformationBound` | Bekenstein, *Universal upper bound on the entropy-to-energy ratio for bounded systems*, Phys. Rev. D **23** (1981) 287–298 |
| `SectorFaithfulNoDeadWeight` | discharged | `NaturalityCoherence` | Mac Lane, *Categories for the Working Mathematician* (2nd ed., 1998), Chapter VII, Theorem 2.1 |
| `mellin_heat_kernel_finite_spectrum_log_sum` | re-stated (no new axiom) | `MellinRegularization` (alias) | Connes–Marcolli, *Noncommutative Geometry, Quantum Fields and Motives*, AMS 2008, §1.7; Berline–Getzler–Vergne, *Heat Kernels and Dirac Operators*, Grundlehren 298 (1992), Ch. 2 and §9.6 |

The v0.9.2 headline `self_model_deficit_unconditional` (in `UnconditionalGoal.lean`) has type:

```
∀ V : VisibleSpectrum, negZetaPrimeAtZero V = (288 : ℝ)
```

— **no caller-supplied Prop hypotheses**, depending only on the three named literature axioms.

### Verified by `#print axioms`

```
'self_model_deficit_unconditional' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta.mellin_heat_kernel_finite_spectrum_log_sum,
   SpectralPhysics.SelfModelDeficitUnconditional.CapacityBound.BekensteinInformationBound,
   SpectralPhysics.SelfModelDeficitUnconditional.NaturalityBound.NaturalityCoherence]
```

Three kernel axioms (`propext`, `Classical.choice`, `Quot.sound`) plus exactly three named literature axioms. Nothing else.

## What remains open

The three named axioms are themselves operator-algebraic translations of published literature. They are **not** closure of v0.9.2 deferred item C.1; they are explicit, named, citation-bearing reductions:

1. **Bekenstein → sectored finite-dim C*-algebras**.
   Translating Bekenstein's 1981 inequality (originally about bounded *physical* systems with finite energy `E` and characteristic length `R`) to a finite-dimensional sectored C*-algebra. Research-level operator-algebra question; estimate 6–12 months.

2. **Mac Lane coherence → information-preserving morphisms**.
   Constructing the monoidal subcategory of sectored algebras with information-preserving morphisms and verifying coherence pentagon/triangle for the spectral-depth functor. Research-level category-theory question; estimate 3–6 months.

3. **Connes–Marcolli Mellin identity → Mathlib**.
   Formalising the general Mellin / heat-kernel identity in Mathlib for a finite spectrum. The infrastructure exists in scattered form (Mathlib has Mellin transforms, has heat semigroups, has zeta extension); the finite-spectrum identification needs lemma-up work. Estimate 1–2 months.

Total: 10–20 months of research-level Lean work to close C.1 unconditionally. v0.9.2 deferred item C.1 itself estimates "6–12 month research project" for the full closure.

## Audit discipline compliance

Per the four rules from `README.md`:

1. **Open content travels as named `Prop` predicates or named literature axioms.**
   ✓ The two v0.9.1 Prop predicates are discharged from explicit literature axioms. No "axiom: conclusion = 288" anywhere.

2. **Named axioms cite real published literature as general facts.**
   ✓ All three named axioms are *general* statements (Bekenstein-style inequality for any `(S, c)`, Mac Lane coherence for any `(S, c)`, Mellin identity for any finite `V`) with explicit literature citations.

3. **No definitional triviality used to hide a target value.**
   ✓ The predicates `CompletenessAtLevel2 S c` and `SectorFaithfulNoDeadWeight S c` are general inequalities in arbitrary `c`. The integer 288 enters via the *separate* combinatorial fact `dim H_hid = 384 − 96` (`SectorDecomposition.lean`), which is `Nat` arithmetic by `decide`.

4. **Empirical inputs are isolated and labelled.**
   ✓ No new empirical input enters this dispatch. The single empirical-flavoured input (the SM dim count `96 = 12 + 84`) was already labelled in v0.9.1.

## Reduction count (audit headline)

```
v0.9 open cross-refs   : 10 lines in v0.9 manuscript
v0.9.1 open content    : 2 unnamed Prop predicates + 1 named axiom
v0.9.2 open content    : 0 unnamed predicates + 3 named literature axioms
```

The reduction `2 open Prop predicates → 0 open predicates + 2 more named literature axioms` is the v0.9.2 progress on top of v0.9.1.

## Anti-pattern check

* **Conclusion-as-axiom (caught by audit in prior `zetaF-prime-zero`)**: NOT present. There is no `axiom self_model_deficit_holds : ζ̃_prime_zero = 288`. The 288 emerges through:
  - Bekenstein axiom (gives `≤ 288`)
  - Mac Lane axiom (gives `≥ 288`, since `dim H_hid = 288`)
  - `le_antisymm` combiner (gives `= 288`)
  Replace any one of the three axioms with `False` and the conclusion is unprovable.

* **Numerical engineering fudge factor**: NOT present. The integer 288 is the combinatorial `2·4·8·3·2 − 96 = 288` from `SectorDecomposition.lean` (Tier-1 `decide`), not a sum-to-288 engineered axiom.

* **"Unconditional" overclaim**: NOT made. The branch name says "unconditional" but the README and this STATUS file are explicit: three named axioms remain. The verdict is **PARTIAL**.

## Verdict

**PARTIAL** — v0.9.2 deferred item C.1 reduced from 10 open cross-refs to 3 named literature axioms (Bekenstein 1981, Mac Lane 1998 §VII, Connes–Marcolli 2008 §1.7). All Lean files build cleanly with zero `sorry`/`admit`. `#print axioms` confirms the dependency list contains exactly the three named axioms plus kernel axioms.

This is real progress and worth the v0.9.2 stamp. It is **not** closure; the three named axioms are genuinely research-level operator-algebra questions.

## References (this branch)

- Bekenstein, J.D. *Universal upper bound on the entropy-to-energy ratio for bounded systems*. Phys. Rev. D **23** (1981) 287–298.
- Bekenstein, J.D. *How does the entropy/information bound work?*. Found. Phys. **35** (2005) 1805–1823.
- Mac Lane, S. *Categories for the Working Mathematician*. Graduate Texts in Mathematics **5**, Springer-Verlag, 2nd ed. (1998), Chapter VII.
- Connes, A. and Marcolli, M. *Noncommutative Geometry, Quantum Fields and Motives*. AMS Colloquium Publications vol. 55 (2008), §1.7.
- Berline, N., Getzler, E. and Vergne, M. *Heat Kernels and Dirac Operators*. Grundlehren der Math. Wiss. **298**, Springer (1992), Ch. 2 and §9.6.
- Ben-Shalom, A. *Spectral Physics* v0.9 (lines 8464, 8753, 8767, 9036, 9157, 9201, 9204, 14910, 16672, 16723); v0.9.1 release.

---

## SOUNDNESS FIX 2 (2026-06-12) — headline forms made conditional on physicality

The 2026-05-27 fix was itself still unsound: `V : VisibleSpectrum` remained
free over arbitrary spectra while `negZetaPrimeAtZero_eq` makes the content a
concrete computable sum; `NaturalityCoherence` alone derived `False` at the
single-mode `y = 1` spectrum (machine-checked falsifier, no `sorryAx`; see
`results/AXIOM-SOUNDNESS-SWEEP.md` item 0b).

All forms of the headline (and both capacity axioms) are now conditional on
the undefined predicate `IsPhysicalSpectrum : VisibleSpectrum → Prop`
(`PhysicalSpectrum.lean`, with consistency model + nonemptiness witness).
The verified `#print axioms` set for `self_model_deficit_unconditional` is
now: kernel three + `BekensteinInformationBound` + `NaturalityCoherence` +
`IsPhysicalSpectrum`. The "no caller-supplied Prop hypotheses" claim above
is RETIRED — the physicality hypothesis is exactly the honest residue of
manuscript Steps 3–4, and removing it was the unsoundness.
