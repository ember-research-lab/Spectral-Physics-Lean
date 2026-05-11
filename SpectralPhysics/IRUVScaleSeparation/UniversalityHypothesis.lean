/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.IRUVScaleSeparation.LowEigenvalueRestriction

/-!
# Spectral Universality — v0.9 Line 1437 as a `Prop`

The v0.9 manuscript's `prop:spectral-convergence` (line 1437) is the
**spectral analogue of the universality hypothesis in statistical
mechanics**. In modern language:

  > For every IR scale `μ > 0`, the low-eigenvalue spectrum of the
  > family `D_F(Λ)` is independent of `Λ` for `Λ ≥ Λ_IR`.

This file *states* that claim as a `Prop` predicate over a
`CutoffFamily`. **The predicate is NOT axiomatised** — it is the
*target* of the universality program, not a free input.

Downstream theorems in this directory then close `SpectralUniversality`
*conditionally*, given named hypotheses:

* `KatoStability.lean` — closes `SpectralUniversality` given a
  Schatten-norm UV-suppression rate (Kato 1966/1995 §V on
  relative-bounded perturbations + Reed-Simon Vol. IV §XIII.5).
* `WilsonPolchinskiConnection.lean` — identifies
  `SpectralUniversality` with Wilson-Polchinski RG-flow convergence
  via a named axiom (Wilson 1971 + Polchinski 1984).

## Anti-pattern — explicitly NOT used

We **do not** write `def SpectralUniversality R := True`. That would
make universality definitionally trivial. We also **do not** axiomatise
`∀ R, SpectralUniversality R`. Spectral universality is the *open
content*; it travels as a hypothesis through every theorem that uses it.

## References

* Ben-Shalom (2026). *Spectral Physics* v0.9, line 1437.
* Wilson, K.G. (1971). *Renormalization group and critical phenomena.*
  Phys. Rev. B **4**, 3174; *Renormalization group and strong
  interactions*, Phys. Rev. D **3**, 1818.
* Polchinski, J. (1984). *Renormalization and effective Lagrangians.*
  Nucl. Phys. B **231**, 269–295. — modern formulation of the
  Wilsonian IR/UV separation.
* Kato (1995) §V (Perturbation theory for closed operators).
* Reed–Simon Vol. IV (1978), Ch. XIII (Spectral analysis).
-/

namespace SpectralPhysics.IRUVScaleSeparation

/-! ## The spectral-universality target -/

/-- **Spectral universality (v0.9 line 1437).**

    A cutoff family `R` exhibits **spectral universality** iff its
    low-eigenvalue spectrum is `Λ`-independent at every IR scale
    `μ > 0`: the IR stability `IRStability R μ` holds for every
    positive `μ`.

    This is the predicate target of the universality program. We
    carry it as a `Prop` predicate. It is **not** axiomatised — every
    theorem that concludes `SpectralUniversality R` does so
    *conditionally*, consuming named-axiom hypotheses with literature
    citations. -/
def SpectralUniversality (R : CutoffFamily) : Prop :=
  ∀ (μ : ℝ), 0 < μ → IRStability R μ

/-! ## Basic structural lemmas — keeping universality non-trivial -/

/-- **Universality is *symmetric* in `Λ ↔ Λ'`.**  Given
    `SpectralUniversality R`, the low-mode restrictions agree for any
    pair `Λ, Λ'` above the IR scale, with no orientation assumption. -/
theorem SpectralUniversality.symmetric
    {R : CutoffFamily}
    (h : SpectralUniversality R)
    (μ : ℝ) (hμ : 0 < μ)
    (Λ Λ' : ℝ) (hΛ : R.Λ_IR ≤ Λ) (hΛ' : R.Λ_IR ≤ Λ') :
    LowEnergyAgree R μ Λ Λ' :=
  (h μ hμ).symmetric Λ Λ' hΛ hΛ'

/-- The "obvious" specialisation: for any single `Λ ≥ Λ_IR`,
    the low-mode spectrum agrees with itself at every scale. This is
    automatic and **does not** discharge `SpectralUniversality`. It is
    here only to confirm reflexivity. -/
theorem SpectralUniversality.refl_pointwise
    (R : CutoffFamily) (μ : ℝ) (Λ : ℝ) :
    LowEnergyAgree R μ Λ Λ :=
  LowEnergyAgree.refl R μ Λ

/-! ## Forbidden anti-patterns explicitly recorded

We record the two audit-discipline forbidden anti-patterns as
*proven non-theorems* (i.e. statements we deliberately do not prove,
documented here as comments).

  -- ANTI-PATTERN 1 (forbidden):
  --   def SpectralUniversality R := True
  -- This would make universality discharge by `trivial`. We do NOT
  -- use it; the definition above is in terms of `IRStability`.
  --
  -- ANTI-PATTERN 2 (forbidden):
  --   axiom universality_holds : ∀ R, SpectralUniversality R
  -- This would make universality a free axiom. We do NOT introduce
  -- such an axiom anywhere in this directory.

If `SpectralUniversality R` is to be concluded for some `R`, it must
be done via a conditional theorem with named-axiom hypotheses
(`spectral_universality_from_perturbation_bound` in `KatoStability.lean`).
-/

end SpectralPhysics.IRUVScaleSeparation
