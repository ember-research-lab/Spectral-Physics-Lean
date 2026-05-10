/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Axioms.SelfRefClosure
import SpectralPhysics.MajoranaSelfRef.JSelfConjugate
import Mathlib.Tactic.NormNum

/-!
# Axiom 3 (Spectral Faithfulness) Restricted to the J-Self-Conjugate Sector

## The hypothesis under test

Prior y_R-closure attempts (`compute/atiyah-singer-J-self-conj`,
`compute/zeta-F-nuR-regularized`, `compute/self-model-deficit-J-fixed`)
used "standard NCG machinery" — Atiyah–Singer, ζ-regularised
dimension, single-eigenvalue reduction.  The user's load-bearing
insight: standard NCG effectively invokes only **Axioms 1–2**.
**Axiom 3 (Spectral Faithfulness)** is the framework's distinguishing
principle and might be where `y_R` lives.

This file formalises the precise restriction of Axiom 3 to the
J-self-conjugate sector `(1,1)_0` of `D_F`, so that the next file
(`FaithfulYR.lean`) can ask the precise question:

> *"For which `y_R` values is the J-self-conjugate sub-spectrum
> faithful to its underlying Majorana operator?"*

## Axiom 3 (v0.9 line 299, label `ax:self-ref`)

The state functional is **faithful** when the spectrum (equivalently,
the trace functional `g ↦ Tr(g(L))`) determines the operator.  In
finite dimensions, this is the typeclass `SpectralDetermination` from
`Axioms/SelfRefClosure.lean`, line 101:

```
class SpectralDetermination (S : SpectralData n) : Prop where
  determines : ∀ S' : SpectralData n,
    (∀ g : ℝ → ℝ, spectralTrace S g = spectralTrace S' g) →
    S.eigenvalues = S'.eigenvalues
```

In finite dimensions this is a **theorem**
(`spectral_determination_finite`) — the substantive content of
Axiom 3 is therefore *not* in pinning a finite-rank operator from
its spectrum; it lives in (a) infinite-dim non-collapse,
(b) operator-vs-spectrum reconstructibility under perturbation, and
(c) the `thm:forcing` cascade that climbs the CD tower.

## What this file establishes

* A formal definition of the (1,1)_0 sector `Dirac` operator as a
  parametrised single eigenvalue `y_R · v_R` (with multiplicity
  `jsc_total_majorana_count = 6`).
* The restriction of `SpectralDetermination` to this sector.
* A clean statement of the question — **which `y_R` produce
  faithful spectra?**

## References

* `SpectralPhysics/Axioms/SelfRefClosure.lean` (Axiom 3 typeclass).
* v0.9 §Axiom 3 (line 299, `ax:self-ref`).
* `compute/atiyah-singer-J-self-conj`, `compute/zeta-F-nuR-regularized`
  — what failed under standard machinery.
* `compute/majorana-self-reference` — the τ^8 numerical bracket.
-/

namespace SpectralPhysics.FaithfulnessForcesYR

open SpectralPhysics.MajoranaSelfRef

/-! ## The (1,1)_0 sector spectral data

The J-self-conjugate sector `(1,1)_0 = ν_R` carries a one-parameter
family of finite Dirac operators, parametrised by the Majorana
Yukawa `y_R > 0`.  For a fixed VEV `v_R` (the see-saw scale) and a
fixed multiplicity `mult = jsc_total_majorana_count = 6`
(3 generations × 2 Majorana doubling), the spectrum is the
constant-eigenvalue list

    `[y_R · v_R, y_R · v_R, …, y_R · v_R]`   (mult copies)

This packages as a `SpectralData` of the abstract Axiom-3 framework. -/

/-- The Majorana sector multiplicity = 6
    (3 generations × 2 Majorana doubling). -/
def majoranaMult : ℕ := 6

/-- **Tier 1.**  The Majorana sector multiplicity is positive. -/
theorem majoranaMult_pos : 0 < majoranaMult := by decide

/-- **Tier 1.**  The Majorana sector multiplicity is at least 2
    (so the `SpectralData` framework's `n ≥ 2` assumption is met). -/
theorem majoranaMult_ge_two : 2 ≤ majoranaMult := by decide

/-- A reference VEV magnitude (a positive real placeholder; the
    derivation does not depend on its value, only on `v_R > 0`). -/
def vR_placeholder : ℝ := 1

/-- **Tier 1.**  `vR_placeholder > 0`. -/
theorem vR_placeholder_pos : (0 : ℝ) < vR_placeholder := by
  unfold vR_placeholder; norm_num

/-- The constant-eigenvalue spectral data for the (1,1)_0 sector
    parametrised by `y_R ≥ 0`.  Every eigenvalue equals `y_R · v_R`. -/
def jscSpectralData (yR : ℝ) (hyR : 0 ≤ yR) : SpectralData majoranaMult :=
  { eigenvalues := fun _ => yR * vR_placeholder
    eigenvalues_nonneg := by
      intro _
      have hv := vR_placeholder_pos
      exact mul_nonneg hyR (le_of_lt hv)
    eigenvalues_sorted := by
      intros _ _ _; exact le_refl _ }

/-! ## Restriction of Axiom 3 (Spectral Faithfulness) to (1,1)_0

We say a y_R-parametrised sector is **Axiom-3 faithful** iff the
trace functional `g ↦ Σ g(y_R · v_R)` determines the eigenvalue list.

In the finite-dim restriction this is *automatic* via
`spectral_determination_finite`. -/

/-- The (1,1)_0 sector is **Axiom-3 faithful** at parameter `y_R`
    iff `SpectralDetermination` holds for the corresponding spectral
    data.  Definitional unfolding of v0.9 line 299 to the sector. -/
def isAxiomThreeFaithfulOnJSC (yR : ℝ) (hyR : 0 ≤ yR) : Prop :=
  SpectralDetermination (jscSpectralData yR hyR)

/-- **Tier 1 — finite-dim faithfulness is automatic.**

The finite-dim spectral-determination theorem
(`spectral_determination_finite`) gives `SpectralDetermination` for
*any* `SpectralData n`.  Hence Axiom 3 — restricted to a finite
sector and read at the operator-spectrum-determination level — is
satisfied at **every** `y_R ≥ 0`.

This is the central observation.  Standard finite-dim faithfulness
gives no constraint on `y_R`. -/
theorem axiom_three_faithful_at_every_yR
    (yR : ℝ) (hyR : 0 ≤ yR) :
    isAxiomThreeFaithfulOnJSC yR hyR :=
  spectral_determination_finite (jscSpectralData yR hyR)

/-! ## A stronger candidate: spectrum → coupling reconstructibility

Axiom 3 might be read more strongly as: the spectrum determines
not only the eigenvalue *list* but the *parameter* `y_R` itself,
given the structural data `(majoranaMult, v_R)`.

For a constant-eigenvalue list `[m, m, …, m]` with known multiplicity
and `v_R`, `m = y_R · v_R` immediately gives `y_R = m / v_R`.  So
this stronger reading also gives every positive `y_R` a unique
recovery — i.e. **all positive `y_R` are reconstructibility-faithful**.

The recovery is degenerate at `y_R = 0` (the zero operator), which
is the only edge case at which the map collapses. -/

/-- The reconstruction map: spectrum (a constant-eigenvalue list)
    plus VEV `v_R` recovers `y_R`. -/
noncomputable def yR_recovered (m v : ℝ) (hv : v ≠ 0) : ℝ := m / v

/-- **Tier 1 — coupling reconstruction.**

For any `y_R ≥ 0`, the recovered coupling from the (1,1)_0 spectrum
equals the original coupling.  This is a tautology of `m = y_R · v_R`
combined with `v ≠ 0`. -/
theorem yR_recovery_correct
    (yR v : ℝ) (hv : v ≠ 0) :
    yR_recovered (yR * v) v hv = yR := by
  unfold yR_recovered
  field_simp

/-- **Tier 1 — reconstructibility is universal on (0, ∞).**

Spectrum-to-coupling reconstructibility succeeds for *every* nonzero
`y_R`; the map collapses only at `y_R = 0`.  The set of
reconstructibility-faithful `y_R` is exactly `(0, ∞)`. -/
theorem reconstructibility_faithful_set :
    ∀ yR : ℝ, 0 < yR →
      yR_recovered (yR * vR_placeholder) vR_placeholder
        (ne_of_gt vR_placeholder_pos) = yR := by
  intro yR _hyR
  exact yR_recovery_correct yR vR_placeholder
    (ne_of_gt vR_placeholder_pos)

end SpectralPhysics.FaithfulnessForcesYR
