# IRUVScaleSeparation — IR/UV Scale Separation in `prop:spectral-convergence`

**Date:** 2026-05-11
**Branch:** `compute/IR-UV-scale-separation`
**Build:** `lake build SpectralPhysics.IRUVScaleSeparation.Verdict` succeeds (1980 jobs).
**Verdict:** **CONDITIONAL** — spectral universality (v0.9 line 1437,
`prop:spectral-convergence`) is identified with the conjunction of a
named Kato–Reed–Simon bridge predicate plus a Schatten-norm
UV-suppression rate; the Wilson–Polchinski analogy enters as one
axiom of citation.
**v0.9.2 deferred item closed (predicate-conditional form):** J.1
(v0.9 line 1437, *IR/UV scale separation in `prop:spectral-convergence`*).

---

## Files

| File                                  | Lines | Status                                |
| ------------------------------------- | ----: | ------------------------------------- |
| `CutoffFamily.lean`                   |  ~135 | Tier 1, 0 sorry, 0 axiom              |
| `LowEigenvalueRestriction.lean`       |  ~140 | Tier 1, 0 sorry, 0 axiom              |
| `UniversalityHypothesis.lean`         |  ~105 | Tier 1, 0 sorry, 0 axiom              |
| `KatoStability.lean`                  |  ~220 | Tier 1, 0 sorry, 0 axiom              |
| `WilsonPolchinskiConnection.lean`     |  ~165 | Tier 1, 0 sorry, **1 named axiom**    |
| `Verdict.lean`                        |  ~150 | Tier 1, 0 sorry, 0 axiom              |

---

## What got proved Tier 1

### `CutoffFamily.lean` — Structural substrate

* `CutoffFamily` — a positive IR scale `Λ_IR > 0` and a Λ-indexed
  eigenvalue assignment `D_F : ℝ → ℕ → ℝ` with non-negativity above
  `Λ_IR`. Models v0.9's "family of self-adjoint operators indexed by
  UV cutoff."
* `IsNonTrivialFamily` — predicate ruling out the audit-forbidden
  constant-family anti-pattern.
* `IsRegulatorFamily` — predicate carrying v0.9's standing assumption.
* `constant_family_not_regulator` — **Tier 1 theorem**: the constant
  family `D_F(Λ) := 0` is *not* a regulator family. Documents the
  forbidden anti-pattern as a proven non-instance.

### `LowEigenvalueRestriction.lean` — IR-band restriction

* `restrictTo R μ Λ : ℕ → Prop` — the low-eigenvalue band predicate.
* `LowEnergyAgree R μ Λ Λ'` — the substantive content: eigenvalue
  agreement across cutoffs in the low band.
* `LowEnergyAgree.symm`, `LowEnergyAgree.refl` — basic structural
  lemmas (Tier 1, proved).
* **`IRStability R μ`** — the v0.9 IR/UV-separation content at scale `μ`.
* `IRStability.symmetric` — Tier 1: drops the orientation requirement.

### `UniversalityHypothesis.lean` — the v0.9 line 1437 predicate

* **`SpectralUniversality R := ∀ μ > 0, IRStability R μ`** — the
  v0.9 line 1437 universality claim, stated as a `Prop` predicate
  (NOT axiomatised, NOT `def := True`).
* `SpectralUniversality.symmetric`, `SpectralUniversality.refl_pointwise`
  — basic structural lemmas.

### `KatoStability.lean` — the load-bearing conditional theorem

* `SchattenUVSuppression R C α` — predicate, Reed–Simon Vol. IV
  §XIII.5 + Simon 2005 Theorem 3.1: eigenvalue-level shadow of a
  Schatten-norm bound `‖D_F(Λ) − D_F(Λ_IR)‖_p ≤ C/Λ^α`.
  Requires `α > 1` (summability).
* `SchattenUVSuppression.C_pos`, `SchattenUVSuppression.α_gt_one`
  — trivial sanity lemmas.
* `KatoLowModeStability R` — predicate, Kato §V.4.10: low-mode
  eigenvalues constant in Λ above the IR scale.
* `KatoReedSimonBridge R` — the *predicate bridge*
  `SchattenUVSuppression → KatoLowModeStability`. Names Kato 1966/1995
  §V + Reed–Simon Vol. IV §XIII.5 + Simon 2005 Theorem 3.1.
* **`spectral_universality_from_perturbation_bound`** — the
  load-bearing theorem:

  ```lean
  theorem spectral_universality_from_perturbation_bound
      {R : CutoffFamily} {C α : ℝ}
      (h_kato_bridge : KatoReedSimonBridge R)
      (h_schatten : SchattenUVSuppression R C α) :
      SpectralUniversality R
  ```

  **Both hypotheses are load-bearing**: removing `h_kato_bridge`
  breaks the bridge step; removing `h_schatten` removes the
  UV-suppression rate the bridge consumes. Proof: bridge yields
  `KatoLowModeStability`; expand to `IRStability` by applying it at
  each `(μ, Λ, Λ', n)` in the low-mode band.

### `WilsonPolchinskiConnection.lean` — the analogy as a named axiom

* `RGFlowConverges R` — predicate, Wilsonian RG-flow convergence
  (eigenvalue-shadow form: low-mode spectrum independent of UV
  cutoff above the IR scale).
* `WilsonianUniversality R := SpectralUniversality R ↔ RGFlowConverges R`
  — the v0.9 line 1437 *analogy* as a biconditional predicate.
* **`wilson_polchinski_analogy`** — named axiom asserting
  `WilsonianUniversality R` for every `R`. Cites Wilson 1971 +
  Polchinski 1984.
* `rg_flow_from_spectral_universality`,
  `spectral_universality_from_rg_flow` — the two directions of the
  biconditional, each a one-liner from the axiom.
* **`v091_line_1437_conditional_closure`** — combined theorem:
  given the two Kato hypotheses, both `SpectralUniversality R` *and*
  `RGFlowConverges R` hold. Consumes the Wilson axiom once (forward
  direction).

### `Verdict.lean` — packaging

* `verdict_spectral_universality_conditional` —
  `spectral_universality_from_perturbation_bound`.
* `verdict_wilson_polchinski_biconditional` — the named axiom in
  verdict form.
* `verdict_full_closure` — the combined conditional.

---

## Named axioms (with citations)

### `wilson_polchinski_analogy` (WilsonPolchinskiConnection.lean)

```lean
axiom wilson_polchinski_analogy :
    ∀ (R : CutoffFamily), WilsonianUniversality R
```

**Category:** Tier 2 — named axiom of citation.
**Sources:**

* Wilson, K.G. (1971). *Renormalization group and critical phenomena.*
  Phys. Rev. B **4**, 3174. — RG-flow universality, Pt. I.
* Wilson, K.G. (1971). *Renormalization group and strong interactions.*
  Phys. Rev. D **3**, 1818. — IR/UV-separation framing.
* Polchinski, J. (1984). *Renormalization and effective Lagrangians.*
  Nucl. Phys. B **231**, 269–295. — modern formulation of Wilsonian
  IR/UV-separation.
* Wetterich, C. (1993). *Exact evolution equation for the effective
  potential.* Phys. Lett. B **301**, 90. — exact functional RG.

**Why axiomatized.** The Wilson–Polchinski analogy identifies the
*operator-spectral* universality of `D_F(Λ)` with the
*path-integral* universality of the Wilsonian effective action.
Both sides are conventionally read as the same physics; the
identification across formulations is a *structural physics fact*,
not a Mathlib-derivable theorem.

**Honesty check.** The axiom is *load-bearing only inside this
directory*. The headline conditional theorem
`spectral_universality_from_perturbation_bound` **does not consume
it** (`#print axioms` reports only the three standard Lean axioms).
The Wilson axiom is consumed *only* by the two verdicts that
involve `RGFlowConverges`.

---

## Predicate-hypothesis decomposition

The v0.9 line 1437 open content is split into the following
*predicates*, each named with literature citations in its docstring:

| Predicate                            | Carrier file | Cited literature |
| ------------------------------------ | -------------- | ---------------- |
| `IsRegulatorFamily`                  | `CutoffFamily` | Ben-Shalom 2026 v0.9 standing assumption |
| `IsNonTrivialFamily`                 | `CutoffFamily` | Anti-pattern bar (audit-discipline) |
| `IRStability`                        | `LowEigenvalueRestriction` | v0.9 line 1437 content |
| `LowEnergyAgree`                     | `LowEigenvalueRestriction` | v0.9 line 1437 content |
| `SpectralUniversality`               | `UniversalityHypothesis` | v0.9 line 1437 (target) |
| `SchattenUVSuppression`              | `KatoStability` | Reed–Simon Vol. IV §XIII.5, Simon 2005 Theorem 3.1 |
| `KatoLowModeStability`               | `KatoStability` | Kato 1995 Theorem V.4.10 |
| `KatoReedSimonBridge`                | `KatoStability` | Kato §V + Reed–Simon §XIII.5 |
| `RGFlowConverges`                    | `WilsonPolchinskiConnection` | Wilson 1971 + Polchinski 1984 |
| `WilsonianUniversality`              | `WilsonPolchinskiConnection` | Wilson 1971 + Polchinski 1984 |

---

## `#print axioms`

```
'SpectralPhysics.IRUVScaleSeparation.verdict_spectral_universality_conditional' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'SpectralPhysics.IRUVScaleSeparation.spectral_universality_from_perturbation_bound' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'SpectralPhysics.IRUVScaleSeparation.verdict_wilson_polchinski_biconditional' depends on axioms:
  [propext, Classical.choice, Quot.sound, wilson_polchinski_analogy]
'SpectralPhysics.IRUVScaleSeparation.verdict_full_closure' depends on axioms:
  [propext, Classical.choice, Quot.sound, wilson_polchinski_analogy]
'SpectralPhysics.IRUVScaleSeparation.wilson_polchinski_analogy' depends on axioms:
  [propext, Classical.choice, Quot.sound, wilson_polchinski_analogy]
```

**Zero project-level axioms** in the Kato closure chain. The single
named axiom `wilson_polchinski_analogy` is consumed only by the
biconditional verdicts.

---

## Sorries

**None.** Zero `sorry` occurrences across all six files.

---

## What's closed vs open

### Closed (CONDITIONAL)

* The **typing** of `SpectralUniversality R` (v0.9 line 1437) as a
  `Prop` predicate over `CutoffFamily`, with the non-trivial
  `IRStability` content.
* The **conditional closure** of `SpectralUniversality R` from a
  Kato–Reed–Simon bridge predicate + Schatten UV-suppression rate
  (`α > 1`).
* The **identification** of `SpectralUniversality R` with
  `RGFlowConverges R` via the Wilson–Polchinski axiom of citation.
* The **constant-family anti-pattern** as a proven non-instance.

### Open (deferred)

* `KatoReedSimonBridge R` is **not** derived from Mathlib. Kato §V
  eigenvalue stability and Reed–Simon Vol. IV §XIII.5 Schatten
  convergence are not formalised in Mathlib. We carry the bridge as
  a predicate-hypothesis to the load-bearing theorem.
* `SchattenUVSuppression R C α` is **not** shown for any concrete
  `R` arising from v0.9's `D_F` construction. The framework does
  not state an explicit `α`; the predicate parameterises it.
* The Wilson–Polchinski biconditional is an **axiom of citation**,
  not a derivation.

---

## Audit-discipline checklist

* [x] **Rule 1 — predicate hypotheses for open content.**
  Ten `Prop` predicates carry v0.9's open content. No open content
  is asserted as fact.
* [x] **Rule 2 — literature-cited axioms.** The single named axiom
  `wilson_polchinski_analogy` cites Wilson (1971) and Polchinski
  (1984); all predicate-hypotheses cite their literature sources
  in their docstrings (Kato 1995 §V, Reed–Simon Vol. IV §XIII.5,
  Simon 2005 Theorem 3.1).
* [x] **Rule 3 — no definitional triviality.**
  `SpectralUniversality R` is **not** `def := True`. It unfolds to
  `∀ μ > 0, IRStability R μ`, which unfolds to a non-trivial
  agreement condition across cutoffs in the low-mode band. The
  headline theorem consumes both hypotheses via a structural
  unfolding; removing either breaks the proof.
* [x] **Rule 4 — empirical inputs isolated.** The Wilson axiom is
  consumed twice (in the biconditional theorems) and never
  re-derived. No empirical numbers enter this directory.

---

## Anti-patterns explicitly NOT used

* [x] `def SpectralUniversality R := True` — **NOT** used.
  Definition is `∀ μ > 0, IRStability R μ`.
* [x] `axiom universality_holds : ∀ R, SpectralUniversality R` —
  **NOT** introduced anywhere. Conclusion of universality always
  requires the Kato hypotheses.
* [x] `D_F R Λ := D_F_fixed` (constant family) — **NOT** trivialised.
  `constant_family_not_regulator` proves the constant family is
  *not* a regulator family.
* [x] Skipping the Wilson–Polchinski connection — **NOT** skipped.
  The full `WilsonPolchinskiConnection.lean` module carries the
  analogy explicitly.

---

## Build

```
$ lake build SpectralPhysics.IRUVScaleSeparation.Verdict
✔ [1980/1980] Built SpectralPhysics.IRUVScaleSeparation.Verdict
Build completed successfully (1980 jobs).
```

* All six new files compile cleanly.
* No new sorries.
* One named axiom of citation (`wilson_polchinski_analogy`), consumed
  only by the biconditional-verdict theorems; the Kato closure
  reports zero project-level axioms.

---

## Connection to v0.9.2 deferred items

This module closes **J.1** (IR/UV scale separation in
`prop:spectral-convergence`) at the predicate-conditional level. The
related items:

* **J.2** (Trace's native geometry) — out of scope here; v0.9's own
  framing is "central open problem of the framework."
* **J.3** (GJ identification from algebra directly) — separate
  numerical session.

J.1 was the *spectral universality* claim. We close it by:

1. Carrying `SpectralUniversality R` as a `Prop` predicate over a
   non-trivial cutoff family `R`;
2. Proving the load-bearing conditional theorem that
   `SpectralUniversality R` follows from the named Kato–Reed–Simon
   bridge + Schatten UV-suppression rate;
3. Identifying `SpectralUniversality R` with the Wilsonian
   `RGFlowConverges R` via the Wilson–Polchinski axiom of citation.

The framework's *universality claim* is **not proved**. It is
identified with the exact functional-analytic input it requires.
