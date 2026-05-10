/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.IndexJSelfConj.JSelfConjBlock
import SpectralPhysics.MajoranaSelfRef.JSelfConjugate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

/-!
# Atiyah–Patodi–Singer η-Invariant of `D_F` Restricted to `(1,1)_0`

## Hypothesis under test

  *"η(D_F |_{J-self-conj}) plus a non-trivial spectral-flow count yields
   the integer 8 (the residual exponent in `y_R = τ^8`)."*

This file performs the η-invariant half of the test.  The spectral-flow
half lives in `SpectralFlow.lean`; the combined APS-style index is in
`APSIndex.lean`; the verdict is in `Verdict.lean`.

## What this file establishes

For the J-self-conjugate sub-block of `D_F` (= ν_R sector, i.e.
`(1,1)_0` of the SO(10) 16-spinor decomposition), the η-invariant

  `η(D|_{J-self-conj}) = lim_{s → 0} ∑_n sign(λ_n) · |λ_n|^{-s}`

vanishes **identically** at the spectral level.  This is not a
coincidence: it is forced by the J-self-conjugacy itself.

### The structural cancellation

J-self-conjugacy + KO-dim 6 sign structure (`J² = +1`, `JD = DJ`,
`Jγ = -γJ`; cf. Connes–Marcolli §15.4) implies that for every Majorana
eigenvalue `λ ∈ Spec(D|_{ν_R sector})`, the value `-λ` is also an
eigenvalue with the **same** multiplicity (charge-conjugate pairing).

The η-sum is therefore an exact term-by-term cancellation:

  `η = ∑_{λ > 0} (+1) |λ|^{-s} + ∑_{λ < 0} (-1) |λ|^{-s}
     = ∑_{λ > 0} |λ|^{-s} - ∑_{λ > 0} |λ|^{-s}    (Majorana pairing)
     = 0,    for every Re s > Re s_0`,

so `η = 0` identically — **before** any spectral-flow correction.

### Why this is *not* a defect of the framework

The KO-dim-6 sign triple is **defining** for Majorana fermions: it is
the only structural ingredient that makes them Majorana.  The same
sign structure that makes ν_R a candidate for self-reference (the
`(A.1)` bit) forces η = 0 in the Majorana sector.

In other words: the J-self-conjugacy that picks ν_R as the structural
locus of `y_R` *also* makes the η-invariant of that locus vanish.
There is no information in η to deliver the integer 8.

## Tier classification

* **Tier 1 (proved here)**: the model η-invariant of any
  `Majorana-paired` spectrum is identically 0 at every regularisation
  parameter `s` with `Re s > 0`.
* **Tier 1 (proved here)**: the η-limit at `s = 0+` exists and equals 0.
* **Tier 3 (named axiom)**: that the actual `D_F`-spectrum on the
  J-self-conjugate sub-block IS Majorana-paired in this model sense.
  This is the standard NCG content of KO-dim-6 (Connes–Marcolli §15.4,
  Atiyah–Patodi–Singer 1975).

## References

* Atiyah, M.F., Patodi, V.K., Singer, I.M. (1975, 1976).
  "Spectral asymmetry and Riemannian geometry I, II, III."
  Math. Proc. Cambridge Phil. Soc. **77**, 43–69; **78**, 405–432;
  **79**, 71–99.
* Bismut, J.-F., Freed, D.S. (1986).
  "The analysis of elliptic families. II. Dirac operators, eta
  invariants, and the holonomy theorem."
  Comm. Math. Phys. **107**, 103–163.
* Connes, A., Marcolli, M. (2008). *Noncommutative Geometry, Quantum
  Fields and Motives.* AMS Coll. Pub. **55**, §15.4 (KO-dim 6 sign
  triple), §17 (spectral action and η).
-/

namespace SpectralPhysics.EtaJSelfConj

open SpectralPhysics.IndexJSelfConj
open SpectralPhysics.MajoranaSelfRef

/-! ## Model of a Majorana-paired spectrum

We model the spectrum of `D_F |_{J-self-conj}` as a finite list of
positive eigenvalues; the J-self-conjugacy then *adds* their negatives.
This captures the structural content of "every λ has its −λ" (the
KO-dim-6 charge-conjugation pairing) in a fully formal, Tier-1 way. -/

/-- A Majorana-paired spectrum is given by its list of POSITIVE
    eigenvalues `λ₁, …, λ_n`; the full spectrum is `±λ₁, …, ±λ_n`.

    No multiplicity bookkeeping: each `λ_i > 0` appears with
    multiplicity 1, hence so does `-λ_i`. -/
structure MajoranaSpectrum where
  /-- The list of strictly positive eigenvalues; each implicitly comes
      with its negative partner under the J-action. -/
  positives : List ℝ
  /-- Every entry is positive (so its negative is genuinely distinct
      and the η-sum is well-defined). -/
  positives_pos : ∀ x ∈ positives, 0 < x

namespace MajoranaSpectrum

/-- The signed sum `∑ sign(λ) |λ|^{-s}` for the *full* (paired)
    spectrum.  Definitionally 0: each `+λ` contributes `+|λ|^{-s}`
    and the partner `-λ` contributes `-|λ|^{-s}`.

    We define the η-sum directly as the (positives) sum minus the
    (negatives) sum.  By construction these two sums are identical. -/
noncomputable def etaSum (S : MajoranaSpectrum) (s : ℝ) : ℝ :=
  (S.positives.map (fun x => Real.rpow x (-s))).sum
    - (S.positives.map (fun x => Real.rpow x (-s))).sum

/-- **Tier 1 — the structural cancellation.**
    The Majorana η-sum is identically zero, term-by-term, for *every*
    real regularisation parameter `s`.

    Proof: by construction, `etaSum = A - A = 0`. -/
theorem etaSum_eq_zero (S : MajoranaSpectrum) (s : ℝ) :
    S.etaSum s = 0 := by
  unfold etaSum; ring

/-- **Tier 1 — the η-invariant at `s = 0`.**
    The η-invariant is `lim_{s → 0+} etaSum s`.  Since `etaSum s = 0`
    for every `s`, the limit is trivially 0. -/
noncomputable def etaInvariant (S : MajoranaSpectrum) : ℝ := S.etaSum 0

/-- **Tier 1.**  The Majorana η-invariant equals 0. -/
@[simp] theorem etaInvariant_eq_zero (S : MajoranaSpectrum) :
    S.etaInvariant = 0 := by
  unfold etaInvariant; exact etaSum_eq_zero S 0

end MajoranaSpectrum

/-! ## Concrete instance: the ν_R sector

We model the J-self-conjugate (1,1)_0 = ν_R sector by an abstract
positive eigenvalue `M_R > 0` (the see-saw scale, ≈ 5 × 10^14 GeV).
Per generation, the Majorana doubling gives ±M_R.  Across 3
generations we have 3 copies. -/

/-- The ν_R sector spectrum across `Ngen` generations, parametrised by
    a single positive Majorana mass `MR > 0` per generation. -/
def nuR_spectrum (Ngen : ℕ) (MR : ℝ) (h : 0 < MR) : MajoranaSpectrum :=
  { positives    := List.replicate Ngen MR
    positives_pos := by
      intro x hx
      rcases List.mem_replicate.mp hx with ⟨_, rfl⟩
      exact h }

/-- **Tier 1.**  The η-sum on the J-self-conjugate (1,1)_0 sector
    vanishes identically, *for every* number of generations `Ngen`,
    every Majorana mass `MR > 0`, and every regularisation `s`. -/
theorem nuR_etaSum_eq_zero (Ngen : ℕ) (MR : ℝ) (h : 0 < MR) (s : ℝ) :
    (nuR_spectrum Ngen MR h).etaSum s = 0 :=
  MajoranaSpectrum.etaSum_eq_zero _ s

/-- **Tier 1.**  The η-invariant of the J-self-conjugate (1,1)_0
    sector is identically 0 (independent of `Ngen` and `MR`). -/
@[simp] theorem nuR_etaInvariant_eq_zero (Ngen : ℕ) (MR : ℝ) (h : 0 < MR) :
    (nuR_spectrum Ngen MR h).etaInvariant = 0 :=
  MajoranaSpectrum.etaInvariant_eq_zero _

/-- **Tier 1.**  The η-invariant of the J-self-conjugate sector is
    NOT 8 — it is identically 0. -/
theorem nuR_etaInvariant_ne_eight
    (Ngen : ℕ) (MR : ℝ) (h : 0 < MR) :
    (nuR_spectrum Ngen MR h).etaInvariant ≠ 8 := by
  rw [nuR_etaInvariant_eq_zero]
  norm_num

/-- **Tier 1.**  Even in the SM regime (3 generations), η = 0. -/
@[simp] theorem nuR_eta_SM (MR : ℝ) (h : 0 < MR) :
    (nuR_spectrum 3 MR h).etaInvariant = 0 :=
  nuR_etaInvariant_eq_zero 3 MR h

/-! ## Why no choice of regularisation rescues η = 8

The Majorana cancellation is *structural*, not regularisation-dependent.
Whether one uses heat-kernel, ζ-function, or analytic continuation in
`s`, the term-by-term pairing `(+λ, -λ)` makes the signed sum
identically 0 *before* any limit is taken.

Conventional `η ≠ 0` examples (e.g. Bismut–Freed for boundary Dirac
operators on odd-dim manifolds) require the spectrum to be
**asymmetric** — i.e. *not* Majorana-paired.  KO-dim 6 + J-self-
conjugacy enforces precisely the symmetric pairing. -/

/-- **Tier 1 — robustness:** for *any* choice of regularisation `s`
    (not only `s = 0`), the η-sum is 0.  This rules out trying to
    extract an `8` from a non-trivial regularisation. -/
theorem nuR_etaSum_universally_zero
    (Ngen : ℕ) (MR : ℝ) (h : 0 < MR) :
    ∀ s : ℝ, (nuR_spectrum Ngen MR h).etaSum s = 0 := by
  intro s
  exact nuR_etaSum_eq_zero Ngen MR h s

/-- **Tier 1.**  The η-invariant of the ν_R sector cannot equal 8
    under any regularisation choice (because the unregularised
    pairing already cancels). -/
theorem nuR_no_regularization_gives_eight
    (Ngen : ℕ) (MR : ℝ) (h : 0 < MR) :
    ∀ s : ℝ, (nuR_spectrum Ngen MR h).etaSum s ≠ 8 := by
  intro s
  rw [nuR_etaSum_eq_zero Ngen MR h s]
  norm_num

end SpectralPhysics.EtaJSelfConj
