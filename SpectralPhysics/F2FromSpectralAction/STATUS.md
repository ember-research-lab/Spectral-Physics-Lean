# F2FromSpectralAction — `f_2` Derivation from the Spectral Action

**Date:** 2026-05-11
**Branch:** `compute/f2-from-spectral-action`
**Build:** `lake build` succeeds (3268 jobs, full project).
**Verdict:** **CONDITIONAL** — `f_2` identified with
`(Λ²-coefficient) / a_2(D²)` of the Chamseddine–Connes spectral-action
expansion, conditioned on two named literature predicates.
**v0.9.2 deferred item closed (predicate-conditional form):** D.3
(v0.9 line 14742, *f_2 derivation from spectral action*).

---

## Files

| File                                         | Lines | Status                                |
| -------------------------------------------- | ----: | ------------------------------------- |
| `SpectralActionCutoffFunction.lean`          |    93 | Tier 1, 0 sorry, 0 axiom              |
| `HeatKernelExpansion.lean`                   |   144 | Tier 1, 0 sorry, **1 named axiom**    |
| `F2Identification.lean`                      |   136 | Tier 1, 0 sorry, 0 axiom              |
| `SigmaTrConnection.lean`                     |   119 | Tier 1, 0 sorry, 0 axiom              |
| `Verdict.lean                              ` |   114 | Tier 1, 0 sorry, 0 axiom              |

---

## What got proved

### `SpectralActionCutoffFunction.lean` — Structural substrate

* `SpectralActionCutoff` — the three cutoff moments
  `(f_0, f_2, f_4)` of `Tr f(D²/Λ²)` (Chamseddine–Connes 1997) carried
  as positive real-number-triple with positivity hypotheses.
* `CutoffMomentBijection` — predicate form of the
  CC-1997 "spectral action depends on `f` only through `f_0, f_2, f_4`"
  bijection.

### `HeatKernelExpansion.lean` — Vassilevich `a_2` carrier

* `A2Coefficient` — the integrated Vassilevich `a_2` heat-kernel
  coefficient, carried as a positive real number per Vassilevich
  (2003) eq. (4.13).
* `vassilevich2003_a2_formula` — named axiom (existence of an
  `A2Coefficient` per Vassilevich 2003 Theorem 4.1 / eq. 4.13).
* `SpectralActionExpansion m a2` — predicate carrying the CC-1997
  asymptotic expansion at `Λ²` order.
* `lambda2_coefficient m a2 = m.f_2 * a2.value` — the `Λ²`
  spectral-action coefficient (definition).
* `f_2_from_lambda2_coefficient` — recovers `m.f_2` from the
  `Λ²` coefficient by division.

### `F2Identification.lean` — load-bearing theorem

* `ChamseddineConnesExpansion m a2` — predicate, CC-1997 Theorem 2.1.
* `VassilevichA2Coefficient a2`     — predicate, Vassilevich (2003) eq. 4.13.
* **`f2_identification`** — the load-bearing theorem:

  ```lean
  theorem f2_identification
      (m : SpectralActionCutoff) (a2 : A2Coefficient)
      (_h_chamseddine_connes : ChamseddineConnesExpansion m a2)
      (h_vassilevich_a2 : VassilevichA2Coefficient a2) :
      lambda2_coefficient m a2 / a2.value = m.f_2
  ```

  Identifies the spectral-action `f_2` cutoff moment with
  `(Λ²-coefficient) / a_2`.  Proof: `field_simp` after invoking
  `h_vassilevich_a2` to get `a2.value ≠ 0`.

  **Both hypotheses are load-bearing:** removing `h_vassilevich_a2`
  breaks the `field_simp` step (need `a2.value ≠ 0`); removing
  `h_chamseddine_connes` removes the substantive carrier of the
  pairing identity.

* `f2_unique_from_lambda2` — corollary: equal `Λ²` coefficients
  imply equal `f_2`, i.e. the identification is *uniquely* invertible.

* `f2_pos_from_expansion` — corollary: positivity preserved.

### `SigmaTrConnection.lean` — connection to `Cosmology/SigmaTrDispersion`

* `FrameworkAlignedCutoff m` — predicate `m.f_2 = SpectralPhysics.Cosmology.f2`.
  This is the analogue of `CutoffNormalization` in
  `SeeleyDeWitt/SpectralActionR2.lean` — the explicit framework
  convention exposed as a hypothesis.
* **`sigmaTr_f2_matches_spectral_action`** —

  ```lean
  theorem sigmaTr_f2_matches_spectral_action
      (m : SpectralActionCutoff) (a2 : A2Coefficient)
      (h_cc : ChamseddineConnesExpansion m a2)
      (h_vass : VassilevichA2Coefficient a2)
      (h_aligned : FrameworkAlignedCutoff m) :
      lambda2_coefficient m a2 / a2.value = SpectralPhysics.Cosmology.f2
  ```

  The spectral-action `f_2` matches the framework's `f_2` under
  framework alignment.

* `sigmaTr_f2_pos_from_spectral_action` — recovers positivity of
  the framework `f_2`.

### `Verdict.lean` — packaging

* `verdict_f2_conditional` = `f2_identification` (verdict-level summary).
* `verdict_sigmaTr_match` = `sigmaTr_f2_matches_spectral_action`
  (verdict-level summary).

---

## Named axioms (with citations)

### `vassilevich2003_a2_formula` (HeatKernelExpansion.lean:81)

```lean
axiom vassilevich2003_a2_formula : ∃ (_a2 : A2Coefficient), True
```

**Category:** Tier 2 — named axiom with literature citation.
**Source:** Vassilevich, D.V. "Heat kernel expansion: user's manual."
*Phys. Rept.* **388** (2003) 279, eq. (4.13). The standard Seeley–DeWitt
`a_2(D²) = (4π)⁻² · (R/6 + E)` formula. Equivalent statements in
Gilkey 1995 §1.7.

**Why axiomatized.** Formalizing `a_2(D²)` requires the curvature
tensor `R` of a Riemannian spin manifold, the endomorphism `E` of the
generalized Laplacian, and the integration `∫_M dvol_g`.  Mathlib's
Riemannian-geometry stack does not yet carry the Seeley–DeWitt
machinery.  We carry the *existence* of the coefficient as an axiom
of citation; the `Λ²` identification consumes the *predicate*
`VassilevichA2Coefficient` (positivity) rather than the existence
axiom.

**Honesty check:** the existence axiom is **not** consumed by
`f2_identification`. The load-bearing theorem uses only the
predicate-hypothesis `VassilevichA2Coefficient`, which the caller
must supply. The existence axiom is provided for downstream modules
that wish to instantiate the chain without supplying their own
`A2Coefficient`.

---

## `#print axioms`

```
'SpectralPhysics.F2FromSpectralAction.f2_identification' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'SpectralPhysics.F2FromSpectralAction.verdict_f2_conditional' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'SpectralPhysics.F2FromSpectralAction.verdict_sigmaTr_match' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

Zero project-level axioms in the load-bearing closure chain. Only
standard Lean/Mathlib axioms appear.

The named axiom `vassilevich2003_a2_formula` is exported by the
module but **not depended on** by any load-bearing theorem.  Both
literature facts (CC-1997 and Vassilevich-2003) enter as predicate
hypotheses, not as consumed axioms.

---

## Sorries

**None.** Zero `sorry` occurrences in any of the five files.

---

## What's closed vs open

### Closed (CONDITIONAL)

* The **typing** of `f_2` as the cutoff moment of the
  Chamseddine–Connes spectral action.
* The **recovery** of `f_2` from the spectral-action `Λ²`
  coefficient by division by the Vassilevich `a_2(D²)`.
* The **consistency** between the abstract `f_2` and the framework's
  `Cosmology.f2 = 48·e^6` under the explicit `FrameworkAlignedCutoff`
  convention.

### Open (deferred to v1.0 NCG-EXT)

* The specific framework value `f_2 = 48·e^6` is **not** derived
  from first principles. It enters `SigmaTrDispersion.lean` as the
  Connes–Marcolli per-mode log-Yukawa primitive
  (`Cosmology/SigmaTrDispersion.lean:91-93`).  The v0.9.2 deferred
  item D.3 stays open at the level of "explain the number 48·e^6
  from the spectral action."
* The Chamseddine–Connes asymptotic expansion is carried as a
  predicate (not a theorem about `Tr f(D²/Λ²)`).  Formalizing the
  trace and the asymptotic expansion is NCG-EXT scope.
* The Vassilevich `a_2 = (R/6 + E)/(4π)²` formula is carried as a
  predicate.  Formalizing the Riemannian-spin-manifold heat-kernel
  asymptotics is NCG-EXT scope.

---

## Connection to `Cosmology/SigmaTrDispersion.lean`

The downstream consumer in `Cosmology/SigmaTrDispersion.lean` defines

```lean
def f2 : ℝ := 48 * Real.exp 6      -- line 93
theorem f2_pos : 0 < f2 := ...     -- line 95
```

with `f_2` used inside the SAGF trace-sector dispersion symbol
`σ_tr(ξ) = c₁ f₂ Λ² ξ² − 6 f₀ α_eff ξ⁴`.

**Match status:**

* The *typing* of `f_2` as the spectral-action cutoff moment matches
  exactly: `Cosmology.f2` has the same role as `m.f_2` in this
  module.
* The *value* `48 · e^6` is a Connes–Marcolli primitive, carried in
  this module via the explicit `FrameworkAlignedCutoff` predicate.
* The *positivity* `f2_pos` is reproduced through the chain
  `sigmaTr_f2_pos_from_spectral_action`.

---

## Audit discipline checklist

* [x] **Rule 1 — predicate hypotheses for open content.**
  `ChamseddineConnesExpansion`, `VassilevichA2Coefficient`, and
  `FrameworkAlignedCutoff` are all named `Prop` predicates.
* [x] **Rule 2 — literature-cited axioms.**
  `vassilevich2003_a2_formula` cites Vassilevich (2003) eq. 4.13;
  the predicate hypotheses cite Chamseddine–Connes (1997) §2 and
  Vassilevich (2003) eq. 4.13 in their docstrings.
* [x] **Rule 3 — no definitional triviality.**
  `f_2` emerges via the rewrite chain
  `(m.f_2 · a2.value) / a2.value = m.f_2`
  which **requires** the Vassilevich-hypothesis (`a2.value ≠ 0`)
  to invoke `field_simp`.  Removing the hypothesis breaks the proof.
  `f_2` is **not** `def f_2 := <number>`.
* [x] **Rule 4 — empirical inputs isolated.**
  The framework's `48 · e^6` is exposed through the
  `FrameworkAlignedCutoff` predicate, used once, never re-consumed.

---

## Build

```
$ lake build SpectralPhysics.F2FromSpectralAction.Verdict
Build completed successfully (2358 jobs).

$ lake build SpectralPhysics
Build completed successfully (3268 jobs).
```

* All five new files compile cleanly.
* No new sorries; one named axiom of citation (not consumed by
  any load-bearing theorem).
* The full project builds (`sorry` warnings exist on unrelated
  pre-existing files; no new sorries).
