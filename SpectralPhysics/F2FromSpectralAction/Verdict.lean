/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.F2FromSpectralAction.SigmaTrConnection

/-!
# Verdict — `f_2` from the Spectral Action

## Headline

**CONDITIONAL** — the `f_2` cutoff moment of the spectral action is
identified, by an audit-discipline chain, with the `Λ²` coefficient of
the Chamseddine–Connes spectral-action expansion divided by the
Vassilevich `a_2(D²)` Seeley–DeWitt coefficient.

The conditional hypotheses are **named, cited literature axioms**:

* **Chamseddine–Connes 1997** — the spectral action `Tr f(D²/Λ²)`
  asymptotically expands with `f_2` as the unique `Λ²` cutoff moment.
  Carried as the predicate `ChamseddineConnesExpansion m a2`.
* **Vassilevich 2003 eq. (4.13)** — the Seeley–DeWitt `a_2(D²)`
  coefficient has the form `(4π)⁻² · (R/6 + E)` and is well-defined
  (positive on positive-scalar-curvature manifolds). Carried as the
  predicate `VassilevichA2Coefficient a2`.

There is one named axiom of citation in this module:

* `vassilevich2003_a2_formula` — existence of an `a_2` coefficient
  per Vassilevich (2003) Theorem 4.1 / eq. (4.13). It is *not* used
  in `f2_identification`; the identification consumes the predicate
  hypothesis `VassilevichA2Coefficient`.

This module relies on **0 new axioms** beyond `vassilevich2003_a2_formula`,
since the load-bearing theorem `f2_identification` consumes its two
hypotheses as `Prop` predicates.

## Sibling modules

* `SeeleyDeWitt/A4Coefficients.lean` — Vassilevich `a_4` coefficient,
  the heat-kernel sibling of `a_2`. Same Vassilevich 2003 source.
* `SeeleyDeWitt/SpectralActionR2.lean` — the framework's
  `CutoffNormalization` is the analogue of `FrameworkAlignedCutoff`
  in this module.
* `Cosmology/SigmaTrDispersion.lean` — downstream consumer of `f_2`.
  `f_2 := 48 · e^6` there (Connes–Marcolli per-mode log-Yukawa).

## What is NOT closed

* The specific framework value `f_2 = 48 · e^6` is **not** derived
  from first principles in this module. It enters
  `SigmaTrDispersion.lean` as a Connes–Marcolli primitive. The
  v0.9.2 deferred item D.3 stays open at the level of "explain the
  number 48·e^6 from the spectral action."  What we close: the
  *typing* of f_2 as the spectral-action cutoff moment.
* The Chamseddine–Connes asymptotic expansion is carried as a
  predicate, not as a theorem about `Tr f(D²/Λ²)`. Formalizing the
  trace and the asymptotic expansion as a Mathlib statement is out
  of scope (NCG-EXT scope).

## Audit-discipline checklist

* [x] **Rule 1.** Open content travels as named `Prop` predicates:
      `ChamseddineConnesExpansion`, `VassilevichA2Coefficient`,
      `FrameworkAlignedCutoff`.
* [x] **Rule 2.** The named axiom `vassilevich2003_a2_formula` cites
      Vassilevich (2003) eq. 4.13; the load-bearing theorem
      `f2_identification` consumes literature-named hypotheses.
* [x] **Rule 3.** No definitional triviality: `f_2` emerges via the
      rewrite chain `(m.f_2 · a2.value) / a2.value = m.f_2` which
      uses `a2.value ≠ 0` (the Vassilevich hypothesis) and would
      fail if `a_2` were zero. **The identification is NOT `def
      f_2 := <number>`.**
* [x] **Rule 4.** Empirical inputs isolated: the only "number" in
      the chain is the abstract `m.f_2` in the `SpectralActionCutoff`
      structure; the framework's `48 · e^6` is exposed through the
      `FrameworkAlignedCutoff` predicate, not smuggled in.

## Verdict

**CONDITIONAL** on (a) the Chamseddine–Connes 1997 asymptotic
expansion and (b) the Vassilevich 2003 `a_2` formula, both carried
as named hypothesis predicates with literature citations.
-/

namespace SpectralPhysics.F2FromSpectralAction

/-! ## The verdict, restated as a theorem signature -/

/-- **Verdict — CONDITIONAL.**

    The `f_2` cutoff moment of the Chamseddine–Connes spectral action
    is identified with the `Λ²`-coefficient-divided-by-`a_2` of the
    Seeley–DeWitt heat-kernel expansion, given the two named
    literature predicates.

    This is `f2_identification`, packaged as the verdict-level
    summary statement. -/
theorem verdict_f2_conditional :
    ∀ (m : SpectralActionCutoff) (a2 : A2Coefficient),
      ChamseddineConnesExpansion m a2 →
      VassilevichA2Coefficient a2 →
      lambda2_coefficient m a2 / a2.value = m.f_2 :=
  f2_identification

/-- **Verdict — connection to `Cosmology/SigmaTrDispersion`.**  Under
    the additional `FrameworkAlignedCutoff` convention, the
    spectral-action `f_2` matches the framework's value of `f_2`
    used inside `σ_tr`. -/
theorem verdict_sigmaTr_match :
    ∀ (m : SpectralActionCutoff) (a2 : A2Coefficient),
      ChamseddineConnesExpansion m a2 →
      VassilevichA2Coefficient a2 →
      FrameworkAlignedCutoff m →
      lambda2_coefficient m a2 / a2.value = SpectralPhysics.Cosmology.f2 :=
  sigmaTr_f2_matches_spectral_action

end SpectralPhysics.F2FromSpectralAction
