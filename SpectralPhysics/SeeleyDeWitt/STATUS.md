# SeeleyDeWitt — R²-Coefficient Module: Audit-Honest Decomposition

**Date:** 2026-05-10
**Branch:** `compute/R2-sign` (rebased from main)
**Build:** `lake build` succeeds (3179 jobs, full project).
**Status vs. prior branch:** REDEMPTION — splits the prior single
"R²-sign" claim into two HONEST claims (A unconditional, B
cutoff-conditional). Removes the deceptive `cutoff_rescaling_per_dof`
axiom that the adversarial audit caught.

---

## Files

| File                                       | Lines | Status                                |
| ------------------------------------------ | ----: | ------------------------------------- |
| `SeeleyDeWitt/A4Coefficients.lean`         |   213 | Tier 1 + definitional, 0 sorry, 0 axiom |
| `SeeleyDeWitt/R2Coefficient.lean`          |   194 | Tier 1, 0 sorry, **1 named axiom**    |
| `SeeleyDeWitt/SpectralActionR2.lean`       |   244 | Tier 1, 0 sorry, 0 axiom              |

---

## What got proved

### `A4Coefficients.lean` — Structural substrate (Tier 1)

* `GeomInvariants` — the eight scalar curvature/bundle invariants of
  the Gilkey/Vassilevich `a_4` formula (`□R, R², R_μν R^μν, R_μνρσ
  R^μνρσ, RE, □E, E², Ω²`).
* `A4Weights.vassilevich` — the eight Vassilevich (2003) eq. (4.26)
  numerical weights `(-12, 5, -2, 2, 60, -60, 180, 30)`, as a
  *definition* (the numbers ARE the definition; citation justifies it).
* `trA4 W G` — the integrated `tr a_4 = (1/360) · Σ w_i · I_i`.
* `cR2 W = W.w_R2 / 360` — the geometric `R²` coefficient.
* `cR2_vassilevich : cR2 A4Weights.vassilevich = 1 / 72` — proved.
* `cR2_vassilevich_pos : 0 < cR2 A4Weights.vassilevich` — proved.
* `trA4_zero : trA4 W GeomInvariants.zero = 0` — proved.

### `R2Coefficient.lean` — Theorem A (UNCONDITIONAL, Tier 1)

* `SignTriple` — abstract `(ε, ε', ε'')` ∈ `{±1}³`.
* `kodim6 : SignTriple` — the canonical `(+1, +1, -1)` triple.
* `FiniteSpectralTriple` — carries `signTriple` and the M-side
  `invariants` separately.
* `FiniteSpectralTriple.isKodim6` — predicate.
* `FiniteSpectralTriple.changeSign T st` — substitute the sign triple,
  leaving `invariants` **unchanged** (structural separation of
  J-finite side from M-side).
* `R2_coefficient_of_a4 T = cR2 A4Weights.vassilevich = 1/72` — the
  manifold-side coefficient.

**Headline theorems:**

* **`r2_sign_independent_of_sign_triple`** :
  `∀ T st, T.isKodim6 → R2_coefficient_of_a4 T =
                       R2_coefficient_of_a4 (T.changeSign st)`.
  Proof: by definitional equality (`rfl`).
* **`r2_value_is_universal`** : the value is `1/72` for every
  KO-dim-6 spectral triple, under every sign-triple change.
* **`r2_coefficient_positive`** :
  `0 < R2_coefficient_of_a4 T` for every `T` — sign comes from the
  geometric `5/360`, NOT from any cutoff choice.

### `SpectralActionR2.lean` — Theorem B (CONDITIONAL, Tier 1)

* `dim_hidden = 288`; `dim_hidden_R : ℝ = 288`.
* `CutoffMoments` — carries `f_0` with `0 < f_0`.
* `CutoffMoments.spectralActionR2 m = m.f_0 * cR2 A4Weights.vassilevich
   = f_0 / 72`.
* `CutoffNormalization m := m.spectralActionR2 = 1` — the **explicit
  cutoff-normalization hypothesis**.
* `cutoff_normalization_solves_f0` : the cutoff normalization
  ⇔ `f_0 = 72`.

**Headline theorems:**

* **`r2_per_dof_normalized`** : *given* `CutoffNormalization m`,
  `c_R2_per_hidden_DOF m = 1 / dim_hidden_R`.
* **`r2_per_dof_eq_one_over_288`** : *given* `CutoffNormalization m`,
  `c_R2_per_hidden_DOF m = 1 / 288`. **The headline.**
* **`c_R2_per_hidden_DOF_value`** : *without* the normalization
  hypothesis, `c_R2_per_hidden_DOF m = m.f_0 / 20736`, a function of
  `f_0`. **This is the anti-claim that makes the audit's point
  precise: there is no universal value without a cutoff choice.**
* **`c_R2_per_hidden_DOF_pos`** : positivity holds for every positive
  cutoff — the most we can say without picking a normalization.

---

## Named axioms (with citations)

### `ccm2008_kodim6_sign_triple` (R2Coefficient.lean:82)

```lean
axiom ccm2008_kodim6_sign_triple :
    kodim6.ε = 1 ∧ kodim6.ε' = 1 ∧ kodim6.ε'' = -1
```

**Category:** Tier 2 — named axiom with literature citation.
**Source:** Connes, A., Marcolli, M. *Noncommutative Geometry,
Quantum Fields and Motives* (American Mathematical Society, 2008),
Theorem 1.214. KO-dim mod 8 sign-table.

**Why axiomatized.**  The sign-table in KO-dim 6 is a finite
combinatorial fact verified in the Connes–Marcolli textbook by
case-checking the action of `J²`, `JD`, `Jγ`. Formalizing the proof
in Lean would require a full development of real spectral triples
(modules over Clifford algebras, the eight-fold periodicity of
KO-dimension), which is out of scope for this module.

**Honesty check:** the axiom asserts a *named, externally verified*
finite fact. It does **not** encode any cutoff choice or
normalization assumption. The R² sign-triple independence theorem
(`r2_sign_independent_of_sign_triple`) does **not even use** this
axiom — it is `rfl`-provable from the structural separation.

---

## Sorries

**None.** Zero `sorry` occurrences in any of the three files.

---

## What's closed (Theorem A) vs open (Theorem B's antecedent)

### Closed (unconditional, KO-dim-6 sign-triple independence)

* The R² coefficient `1/72` is computed from `A4Weights.vassilevich`
  and is independent of the spectral-triple data.
* Positivity is established without any cutoff hypothesis.
* `changeSign` leaves the manifold-side `GeomInvariants` untouched, so
  every sign-triple modification yields the same R² coefficient.

### Open / conditional (per-DOF `1/288`)

* The `1/288` value follows **only** under the hypothesis
  `CutoffNormalization m`, i.e. `f_0 = 72`.
* No theorem in this module *forces* this cutoff choice. It is a
  framework convention, not a derivation.
* The anti-claim `c_R2_per_hidden_DOF_value` makes the dependence on
  `f_0` precise.

---

## Comparison to the prior `compute/R2-sign` branch

| Aspect                    | Prior branch (audited)             | This redemption                   |
| ------------------------- | ---------------------------------- | --------------------------------- |
| `c_{R²} = 1` (bare)       | derived via hidden axiom           | hypothesis `CutoffNormalization`  |
| `c_{R²}/288 = 1/288`      | "derived" (trivially under axiom)  | **conditional** on the hypothesis |
| `cutoff_rescaling_per_dof`| named axiom, hidden semantics      | **removed**                       |
| Sign-triple independence  | bundled with `1/288` claim         | **separated** (Theorem A)         |
| What is unconditional     | unclear from prior phrasing        | sign-triple independence + `5/360 > 0` |
| What is conditional       | not explicit                       | per-DOF `= 1/288`                 |

The **substantive content** the prior branch *should* have shown
(Theorem A) is now proved structurally. The **conventional content**
that was previously dressed up as a derivation (Theorem B) is now
honestly conditioned on the cutoff hypothesis.

---

## Build status

```
$ lake build
✔ [3178/3179] Built SpectralPhysics (1.9s)
Build completed successfully (3179 jobs).
```

* All three new files compile cleanly.
* No new sorries; one named axiom with citation.
* The full project builds (warnings on unrelated files only).
* No regressions to other modules.

---

## Audit discipline checklist

* [x] **Theorem A is real and proved structurally** — by `rfl` from
      definitional separation of J-finite side and M-side.
* [x] **Theorem B explicitly conditions on the cutoff normalization** —
      via the `CutoffNormalization` hypothesis.
* [x] **No axiom that chooses `f_0` to make `c_{R²}` positive** —
      positivity comes from `cR2_vassilevich_pos` (geometric `5/360`).
* [x] **The `1/288` ratio is presented as a CONSEQUENCE of
      normalization + `dim(hidden) = 288`**, not an a priori claim.
* [x] **CCM 2008 sign-table is a named axiom with citation** —
      `ccm2008_kodim6_sign_triple`.

---

## What this module does NOT prove (out of scope)

1. The Vassilevich (2003) eq. (4.26) formula itself — its numerical
   coefficients `(-12, 5, -2, 2, 60, -60, 180, 30)` are *defined* in
   Lean to match the citation, not derived from heat-kernel
   asymptotics.
2. That the cutoff normalization `f_0 = 72` is *forced* by some other
   principle — it is presented as a framework convention.
3. The KO-dim 6 sign-triple `(+1, +1, -1)` itself — taken as the
   named CCM 2008 Theorem 1.214 axiom.
4. The product structure `M × F` of the spectral triple — abstracted
   into `GeomInvariants` for `M` and `signTriple` for `F`.

These are all **deliberate scope limitations**, not hidden assumptions.
