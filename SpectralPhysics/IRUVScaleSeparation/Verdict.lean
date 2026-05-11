/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.IRUVScaleSeparation.WilsonPolchinskiConnection

/-!
# Verdict — IR/UV Scale Separation (v0.9 line 1437)

## Headline

**CONDITIONAL** — spectral universality (v0.9 line 1437,
`prop:spectral-convergence`) is identified with the conjunction of
two named functional-analytic predicates:

1. `KatoReedSimonBridge R` — Kato §V eigenvalue stability + Reed–Simon
   Vol. IV §XIII.5 Schatten-norm convergence;
2. `SchattenUVSuppression R C α` — a summable UV-suppression rate
   with `α > 1`.

Given both predicates, `SpectralUniversality R` is concluded *and*
(by the Wilson–Polchinski analogy axiom) is equivalent to Wilsonian
`RGFlowConverges R`.

This verdict is **honest**: it does *not* prove the framework's
universality claim. It *identifies* the exact functional-analytic
input the v0.9 universality hypothesis needs.

## What this directory closes

| v0.9 statement | Closure status | Hypothesis |
| -------------- | -------------- | ---------- |
| `prop:spectral-convergence` (line 1437) — spectral analogue of statistical-mechanics universality | **CONDITIONAL** | `KatoReedSimonBridge` + `SchattenUVSuppression` |

## What this directory does **NOT** close

* `KatoReedSimonBridge R` is *not* derived from Mathlib — it is the
  audit-discipline-named handle on Kato §V + Reed–Simon §XIII.5.
* `SchattenUVSuppression R C α` is *not* shown for any concrete
  family `R` arising from the v0.9 spectral construction. The
  numerical value of `α` is free.
* The Wilson–Polchinski biconditional is an *axiom of citation*
  (`wilson_polchinski_analogy`), not a derivation.

## Named axioms (the entire directory)

| Axiom | Citation | Role |
| ----- | -------- | ---- |
| `wilson_polchinski_analogy` | Wilson 1971 + Polchinski 1984 | Identifies `SpectralUniversality R ↔ RGFlowConverges R` |

There is **one** named axiom in this directory. Three other
load-bearing inputs (`KatoReedSimonBridge`, `SchattenUVSuppression`,
`IsRegulatorFamily`) are **predicate hypotheses**, not axioms.

## Anti-patterns explicitly NOT used

* No `def SpectralUniversality R := True`. The predicate unfolds
  to `IRStability`, which unfolds to a non-trivial agreement.
* No `axiom universality_holds : ∀ R, SpectralUniversality R`.
* No `D_F R Λ := D_F_fixed`. The `CutoffFamily` carries
  `D_F : ℝ → ℕ → ℝ` with non-trivial Λ-dependence; the constant
  family is *not* a regulator family (`constant_family_not_regulator`).
* The Wilson–Polchinski connection is **not** skipped — it is
  carried as the named axiom and used in the `RGFlowConverges`
  half of the headline.

## Audit-discipline checklist

* [x] **Rule 1 — predicate hypotheses for open content.**
  `IsRegulatorFamily`, `IRStability`, `SpectralUniversality`,
  `SchattenUVSuppression`, `KatoLowModeStability`,
  `KatoReedSimonBridge`, `RGFlowConverges`, `WilsonianUniversality`
  are all `Prop`-valued.
* [x] **Rule 2 — literature-cited axioms.** The single named axiom
  `wilson_polchinski_analogy` cites Wilson (1971) and Polchinski
  (1984). The predicate hypotheses cite Kato (1995), Reed–Simon
  (1978), Simon (2005) in their docstrings.
* [x] **Rule 3 — no definitional triviality.** The headline theorem
  consumes both the bridge predicate and the Schatten predicate via
  a structural unfolding chain. Removing either breaks the proof.
  `SpectralUniversality` is **not** `def := True`; it unfolds to
  `∀ μ > 0, IRStability R μ`, which unfolds to a non-trivial
  agreement condition.
* [x] **Rule 4 — empirical inputs isolated.** The single Wilson
  axiom is consumed twice (once per direction of the biconditional)
  but is not used to derive itself. No "empirical numbers" enter
  this directory.

## Verdict

**CONDITIONAL** on the named Kato–Reed–Simon bridge and Schatten
UV-suppression rate. The Wilson–Polchinski analogy enters as one
axiom of citation. The framework's universality claim
(v0.9 line 1437) is honestly identified, not proved.
-/

namespace SpectralPhysics.IRUVScaleSeparation

/-! ## The verdict-level summary statements -/

/-- **Verdict — CONDITIONAL.**  Spectral universality follows from
    the Kato–Reed–Simon bridge predicate plus a Schatten UV-suppression
    rate. This is the audit-discipline closure of v0.9 line 1437.

    Re-exports `spectral_universality_from_perturbation_bound`. -/
theorem verdict_spectral_universality_conditional
    {R : CutoffFamily} {C α : ℝ}
    (h_kato_bridge : KatoReedSimonBridge R)
    (h_schatten : SchattenUVSuppression R C α) :
    SpectralUniversality R :=
  spectral_universality_from_perturbation_bound h_kato_bridge h_schatten

/-- **Verdict — Wilson–Polchinski biconditional.**  The framework's
    spectral universality is identified with Wilsonian RG-flow
    convergence by the named Wilson–Polchinski axiom.

    Re-exports the axiom directly. -/
theorem verdict_wilson_polchinski_biconditional
    (R : CutoffFamily) :
    WilsonianUniversality R :=
  wilson_polchinski_analogy R

/-- **Verdict — combined.**  Given the two named hypotheses, both
    `SpectralUniversality R` *and* `RGFlowConverges R` hold.
    This is the full v0.9 line 1437 closure. -/
theorem verdict_full_closure
    {R : CutoffFamily} {C α : ℝ}
    (h_kato_bridge : KatoReedSimonBridge R)
    (h_schatten : SchattenUVSuppression R C α) :
    SpectralUniversality R ∧ RGFlowConverges R :=
  v091_line_1437_conditional_closure h_kato_bridge h_schatten

end SpectralPhysics.IRUVScaleSeparation
