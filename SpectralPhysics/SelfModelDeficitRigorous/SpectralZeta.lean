/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import SpectralPhysics.SelfModelDeficitRigorous.SectorDecomposition
import SpectralPhysics.SelfModelDeficitRigorous.FaithfulState

/-!
# Spectral Zeta and the Functional Determinant (Honest)

We define `informationContent S = −ζ̃'(0)`, the visible sector's
**spectral depth**.  For a finite-dimensional Dirac operator `D` with
spectrum `{σ_k}` and Yukawa couplings `y_k := σ_k / Λ`, the standard
heat-kernel / Mellin-transform derivation (see Connes–Marcolli 2008,
*Noncommutative Geometry, Quantum Fields and Motives*, §1.7;
Berline–Getzler–Vergne 1992, *Heat Kernels and Dirac Operators*) gives

    ζ̃(s) = ∑_k mult_k · y_k^{-2s},     -ζ̃'(0) = ∑_k mult_k · (-log y_k²)
                                                = ∑_k mult_k · (-2 log y_k).

We rescale by absorbing the factor 2 into the multiplicity convention
(matching v0.9 line 8442): `−ζ̃'_vis(0) = Σ_f mult_f · (−log y_f)`.

## Honesty note

The earlier `compute/zetaF-prime-zero` branch axiomatised the *value*
of this sum to specific rationals (`S_up := 9723/100`, etc.) and then
algebraically observed that the rationals sum to 288. **That is not what
this file does.**

Here:

* `informationContent` is defined as a **sum over the visible spectrum**,
  parameterised by the spectrum itself.  The numerical value of the sum
  is determined by the spectrum, not asserted by axiom.
* The connection to the Mellin transform of the heat kernel is stated
  as a *named theorem* with an explicit `axiom` declaration only for the
  general analytic fact — **not** as an axiom forcing the sum to a
  specific number.

## Main definitions

* `VisibleSpectrum` — finite indexed family of multiplicities + Yukawa values
* `informationContent` — the sum `Σ mult_f · (-log y_f)` (real)

## Named axiom (with citation)

* `mellin_heat_kernel_finite_spectrum_log_sum` — the **general**
  Connes–Marcolli identity: for a finite spectrum, the Mellin transform
  of the heat trace gives `−ζ̃'(0) = informationContent`.  No specific
  numerical value is fixed.

## What this file does NOT do

* It does **not** evaluate `informationContent` to 288 numerically.
* It does **not** axiomatise any rational value for the sum.
* The visible sector's spectrum is a *parameter*; whether its
  `informationContent` equals `dim(H_hid)` is the content of the
  downstream bounds, not of this file.
-/

namespace SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta

open SpectralPhysics.SelfModelDeficitRigorous.SectorDecomposition

/-- A **finite visible spectrum** consists of a finite indexed family
of pairs `(mult_f, y_f)`, where `mult_f` is a positive integer
multiplicity and `y_f > 0` is the corresponding (dimensionless) Yukawa
coupling. -/
structure VisibleSpectrum where
  /-- Number of distinct spectral modes. -/
  numModes : ℕ
  /-- Multiplicity of the `i`-th mode. -/
  mult : Fin numModes → ℕ
  /-- Yukawa value of the `i`-th mode. -/
  yukawa : Fin numModes → ℝ
  /-- Yukawas are strictly positive (required to take `log`). -/
  yukawa_pos : ∀ i, 0 < yukawa i

/-- **Spectral information content** of a visible spectrum:

  `−ζ̃'(0)_vis  :=  ∑_f mult_f · (−log y_f)`.

This is the v0.9 line 8450 expression: "each mode `f` contributes
`−log y_f` units (the spectral analog of Shannon information `−log p`).
The total is the most compressed single-number summary of the visible
spectrum that goes beyond polynomial moments."

The integer `numModes`, the multiplicity function, and the Yukawa
values are all **parameters**.  We *define* `informationContent`
as the sum, not as an axiomatic constant. -/
noncomputable def informationContent (V : VisibleSpectrum) : ℝ :=
  ∑ i : Fin V.numModes, (V.mult i : ℝ) * (-Real.log (V.yukawa i))

/-- Convenient unfolding lemma. -/
@[simp] theorem informationContent_def (V : VisibleSpectrum) :
    informationContent V =
      ∑ i : Fin V.numModes, (V.mult i : ℝ) * (-Real.log (V.yukawa i)) := rfl

/-- **Empty visible spectrum has zero information content.** Pure sanity. -/
theorem informationContent_empty
    (V : VisibleSpectrum) (h : V.numModes = 0) :
    informationContent V = 0 := by
  unfold informationContent
  -- When numModes = 0, Fin 0 is empty, so the sum is 0
  rcases V with ⟨n, mult, yukawa, ypos⟩
  simp only at h
  subst h
  simp

/-- Singleton spectrum with a single mode of multiplicity `m` and
Yukawa `y > 0` contributes `m · (−log y)`. -/
theorem informationContent_singleton
    (m : ℕ) (y : ℝ) (hy : 0 < y) :
    informationContent { numModes := 1
                         , mult := fun _ => m
                         , yukawa := fun _ => y
                         , yukawa_pos := fun _ => hy } =
    (m : ℝ) * (-Real.log y) := by
  unfold informationContent
  simp

/-! ### Named-axiom interface to Mellin / heat-kernel theory

The general analytic identity from Connes–Marcolli §1.7 (and
Berline–Getzler–Vergne 1992):

> For a finite-dimensional self-adjoint operator `D` with spectrum
> `{σ_k}` of multiplicities `{mult_k}` and a chosen scale `Λ`, define
> the zeta function `ζ_D(s) := ∑_k mult_k · (σ_k/Λ)^{-2s}`.  Then
> `ζ_D` extends to a meromorphic function on `ℂ` with `ζ_D(0)` and
> `ζ_D'(0)` finite, and `−ζ_D'(0) = ∑_k mult_k · log((σ_k/Λ)^{-2})
>                                = ∑_k mult_k · (−2 log y_k)` where
> `y_k := σ_k/Λ`.

This is *not* available out-of-the-box in Mathlib (the Mellin
infrastructure exists, but the heat-kernel-zeta identification for
finite spectra is not lemma'd up).  We therefore introduce **one named
axiom**: the existence of a `−ζ̃'(0)` value equal to the
`informationContent`.  Crucially:

* The axiom states a **general identity** — for *any* finite spectrum,
  the `−ζ̃'(0)` value equals the explicit sum.  It does **not** fix
  the sum to any particular number.
* The conclusion of the Self-Model Deficit Theorem (`= 288`) is NOT
  asserted here; it arises only after the *separate* completeness +
  faithfulness bounds in `CompletenessBound.lean` and
  `FaithfulnessBound.lean`. -/

/-- **Named axiom** (Connes–Marcolli 2008, §1.7; Berline–Getzler–Vergne
1992, Ch. 2 + §9.6).  For a finite visible spectrum, the
zeta-regularised value `−ζ̃'(0)` (defined via Mellin transform of the
heat trace `Tr e^{−tD²}`) equals the explicit
`informationContent` sum.

* **What this asserts**: an existence statement — for every
  `VisibleSpectrum V`, there exists a real number `z` (the
  zeta-regularised value) equal to `informationContent V`.
* **What this does NOT assert**: any specific numerical value of
  `informationContent V` for any concrete `V`.  The value depends
  entirely on the Yukawa parameters, which are inputs.
* **Smuggling check**: this axiom does not fix `informationContent`
  to 288 nor to any constant.  It only names the
  Mellin/heat-kernel value as `informationContent`.  If you supply a
  visible spectrum, the sum is what it is. -/
axiom mellin_heat_kernel_finite_spectrum_log_sum
    (V : VisibleSpectrum) :
    ∃ z : ℝ, z = informationContent V

/-- The **functional determinant** at zero, `−ζ̃'_vis(0)`, taken as the
existential value supplied by the named axiom. -/
noncomputable def negZetaPrimeAtZero (V : VisibleSpectrum) : ℝ :=
  Classical.choose (mellin_heat_kernel_finite_spectrum_log_sum V)

/-- The defining property of `negZetaPrimeAtZero`. -/
theorem negZetaPrimeAtZero_eq (V : VisibleSpectrum) :
    negZetaPrimeAtZero V = informationContent V :=
  Classical.choose_spec (mellin_heat_kernel_finite_spectrum_log_sum V)

/-! ### Crucial honesty assertion

`negZetaPrimeAtZero V` depends entirely on the chosen spectrum `V`.
For example, the *single-mode spectrum* with `y = e^{−288}` and
`mult = 1` would give `informationContent = 288` — but that just means
*choosing that single mode forces the sum to 288*, which is the
inverse problem of the Self-Model Deficit Theorem.  It is **not** an
independent derivation of 288.

The actual physics question is: given the SM Yukawa couplings
(electron, muon, ..., top, ...), measured at the electroweak scale,
does the sum land on 288?  v0.9's numerical verification table
(lines 8469–8484) reports that *with PDG inputs* the sum is 288.0 ±
seesaw correction — but that is a *numerical observation*, not a
theorem.  We do not encode that observation in Lean. -/

end SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta
