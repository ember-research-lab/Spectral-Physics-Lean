# Faithfulness-Saturation Lemma — STATUS

**Branch**: `feat/faithfulness-saturation`
**Module**: `SpectralPhysics/SelfModelDeficitRigorous/FaithfulnessSaturation.lean`
**Target**: open problem A (saturation forcing) — the deepest lever of the
program. Formalizes candidate **C3** (`ember-tasks/saturation-forcing/output/`).

## Verdict: **PARTIAL** — reduction CLOSED given O1, O2; O1 and O2 stay OPEN.

This is an honest partial per the falsifier spec
(`ember-tasks/faithfulness-saturation-lemma/falsifier-spec.md`). O2 is **NOT**
discharged.

| Piece | Status |
|---|---|
| Reduction `saturation ⟺ ‖(1−P₃)v‖=‖P₃v‖ ⟺ ε²=2 ⟺ K=2/3` | **CLOSED**, sorry-free, kernel-only axioms |
| Cabibbo transport `saturation ⟹ λ₀=τ/(1+τ) ⟹ λ=(150−23√5)/440` | **CLOSED**, sorry-free, kernel-only |
| O1 — capacity identification (content=`‖(1−P₃)v‖`, capacity=`‖P₃v‖`) | **STATED** as explicit hypotheses (`saturation_reduction`) |
| O2 — no-dead-weight / naturality (`≥` direction) | **OPEN** named residue axiom `naturalityNoDeadWeight`, NOT discharged |
| Headline guard | `IsSelfModeledChannel` (undefined predicate, anti-`288` discipline) |

## What CLOSED (the reduction), sorry-free

The circulant carrier is `√mₖ = M(1 + ε·cos(θ + 2πk/3))`. Proved closed forms:

* `carrierNormSq_eq` : `‖P₃v‖² = 3M²` (democratic mode, from `Σcos = 0`).
* `breakingNormSq_eq` : `‖(1−P₃)v‖² = (3/2)M²ε²`, `θ`-free (from `Σcos²=3/2`).
* `breakingNorm_eq_carrierNorm_iff` : `‖(1−P₃)v‖ = ‖P₃v‖ ⟺ ε² = 2` (M,θ-free).
* `koide_of_epsilonSq_two` : `ε² = 2 ⟹ K = 2/3` (via `KoideFormula.circulant_implies_koide`).
* `cabibbo_leading_of_saturation` / `cabibbo_full_of_saturation` : the same
  `≥` pinch on the inter-unit channel forces `λ/(1−λ)=τ ⟹ λ₀=τ/(1+τ) = cabibboLeading`,
  and `λ = (150−23√5)/440` via `cabibbo_closed_form`.

`breakingNormSq`/`carrierNormSq` are **defined geometrically** (sums of squares
of the carrier vector's coordinates); the closed forms are theorems, not
definitions — nothing trivializes the pinch.

## The two OPEN residues (named, pre-existing; nothing laundered)

* **O1 — capacity identification.** That the intra-multiplet channel's *content*
  is `‖(1−P₃)v‖` and its *capacity* is `‖P₃v‖` (and, for Cabibbo, `ε_total =
  λ/(1−λ)` as content) is a reading — insert `located-gap (b)`, "asserted, not
  yet derived". It travels as the explicit hypotheses `hO1_content`,
  `hO1_capacity` of `saturation_reduction`. STATED, not derived.

* **O2 — no-dead-weight / naturality (`conj:func-det` Step 4).** The `≥`
  direction (`capacity ≤ content`; naturality forbids strict slack) is the
  operator-algebraic content of spectral-physics.tex L13184–13191
  ("dead weight … violating naturality"), rigorous proof open
  (`open:self-model-deficit-proof`). Enters as the named axiom
  `naturalityNoDeadWeight`, **conditional on the guard** `IsSelfModeledChannel`.
  It is a general inequality — mentions no numeral. **NOT discharged.**

O3 (direct-sum naturality scope) was discharged upstream (2026-07-07,
`o3-naturality-scope`) and is used as `def:reconstruction-operator`, not
re-litigated here.

## Guarding — anti-`288` (soundness)

`faithfulness_saturation_lemma` carries `IsSelfModeledChannel ch`; it is **NOT**
`∀ ch, ε²=2` (which is FALSE — quarks, hidden triplet). Mirrors the
`IsPhysicalSpectrum V →` fix that retired the unsound
`∀ V, negZetaPrimeAtZero V = 288` (`SelfModelDeficitUnconditional/Verdict.lean`).
The guard is undefined (no intro rule); consistency model (mirrors
`PhysicalSpectrum`): interpret `IsSelfModeledChannel ch := carrierNorm ch ≤
breakingNorm ch` — the axiom becomes a tautology and the class is nonempty
(`leptonChannel`). So `naturalityNoDeadWeight` cannot derive `False`.

## Non-injectivity location (load-bearing)

`full_map_injective_in_amplitude`: at fixed `M`, `breakingNormSq` determines
`ε²` — the full circulant map `(M,ε,θ) ↔ masses` IS injective. Hence O2's
dead-weight non-injectivity does NOT live in the full map; it lives in the
naturality-restricted complementary/self-model records — inside O2's open
scope, not claimed here. (Asserting non-injectivity on the full map would be
FALSE.)

## Non-vacuity

* **Positive witness** `leptonChannel` (`ε=√2`, `ε²=2`): saturated
  (`leptonChannel_saturates`), `K=2/3` (`leptonChannel_koide`) — kernel-only.
* **Negative control** `quarkChannel` (`ε=3/2`, `ε²=9/4`): NOT saturated
  (`quarkChannel_not_saturated`), ratio `9/8 ≠ 1` (`quarkChannel_ratio`); and
  `IsSelfModeledChannel` is unprovable for it, so the lemma does not predict
  saturation. Firewall against vacuity.
* **Hidden triplet** (`ε_H ≈ 2`, ratio `ε_H²/2 ≈ 2 ≠ 1`): not built as a channel
  (positivity is at the double-wall `min_k(1+εcos)→0` — itself evidence `ε=2` is
  the boundary), documented via `breakingNormSq_eq_ratio`.

A vacuous principle would give ratio 1 everywhere; the pinch is a genuine `iff`.

## `#print axioms` (verified)

```
saturation_reduction               [propext, Classical.choice, Quot.sound]
faithfulness_saturation_lemma      [propext, Classical.choice, Quot.sound,
                                    IsSelfModeledChannel, naturalityNoDeadWeight]
faithfulness_saturation_koide      [propext, Classical.choice, Quot.sound,
                                    IsSelfModeledChannel, naturalityNoDeadWeight]
cabibbo_full_of_saturation         [propext, Classical.choice, Quot.sound]
leptonChannel_koide                [propext, Classical.choice, Quot.sound]
full_map_injective_in_amplitude    [propext, Classical.choice, Quot.sound]
quarkChannel_not_saturated         [propext, Classical.choice, Quot.sound]
```

Kernel + exactly two residue axioms (`IsSelfModeledChannel` guard,
`naturalityNoDeadWeight` = O2). **No axiom pins `ε²`, `K`, `λ`, or a dimension to
a numeral. No gerrymandered no-dead-weight predicate.**

## Symbolic cross-check (sympy, exact)

```
mean = M;  carrierNormSq = 3·M²;  breakingNormSq = (3/2)·M²·ε²
breakingNormSq = carrierNormSq  ⟺  ε² = 2         (ratio = ε²/2)
τ = (5−√5)/10;  λ₀ = τ/(1+τ) = (7−√5)/22
λ  = λ₀·(8+τ)/8 = (150−23√5)/440 = 0.224023719357965538596793194589
```

## Build

`lake build` green (3356 jobs); module builds standalone. Zero `sorry`/`admit`.
Imported into the root at `SpectralPhysics.lean`.
