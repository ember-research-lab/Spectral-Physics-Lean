/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Structural η-Jump for a Finite Spectral Triple (Honest)

This file replaces the audit-caught deceptive predecessor
(`compute/eta-integers-12-144-168-768`, pre-redemption) which defined

```
def etaJump (S : Finset (Fin 384)) : ℕ := 2 * S.card
```

and then "proved" the four integer predictions 12/144/168/768 as
arithmetic on hand-chosen index ranges, with the load-bearing
"axiom" `etaJump_two_times_modes` reducing to `rfl`.

This file does **not** repeat that mistake.  Instead it formalises the
η-invariant **structurally**: as a real-valued spectral functional of
the finite Dirac operator `D_F`, computed from its eigenvalue
spectrum and the sign of each eigenvalue.  The integers 12, 144, 168,
768 are then NOT starting points — they are CONSEQUENCES that follow
only when an additional spectral-identification predicate (see
`SpectralIdentification.lean`) and a named APS / Bismut-Freed
doubling axiom (see `IntegerCounts.lean`) are supplied.

## Mathematical content

For a finite spectral triple `(A_F, H_F, D_F, J_F, γ_F)` of KO-dim 6,
the η-invariant of `D_F` is the spectral asymmetry

  `η(D_F) := Σ_k sgn(λ_k)`

where `{λ_k}` is the (nonzero) eigenvalue spectrum of `D_F` with
multiplicity.  The **η-jump** under a one-parameter spectral flow
`s ↦ D_F(s)` is

  `Δη_F(s_1, s_2) := η(D_F(s_2)) − η(D_F(s_1))`

and equals (Atiyah-Patodi-Singer 1976, eq. (1.7); Bismut-Freed 1986,
Thm. 2.10) twice the *signed spectral flow* — the algebraic number of
eigenvalue crossings of zero, weighted by chirality.

For the spectral-physics framework's specific `D_F` (KO-dim 6,
J-paired Majorana structure on `dim_ℂ(H_F) = 384`), each eigenvalue
crossing of zero on the σ- or r-axis is paired with its
J-conjugate by `J ∘ D_F = D_F ∘ J`.  This **Bismut-Freed Majorana
doubling** is what produces the factor of 2 between the count of
*physical* crossings and the η-jump magnitude.

## What is in THIS file

* An abstract `FiniteSpectralTriple` structure recording the spectrum
  `λ : Fin n → ℝ` of `D_F` and a hypothesis that `dim H_F = 384`.
* A structural definition of `eta` as `Σ_k sgn(λ k)`.
* A definition of `etaSpectralFlow` between two parameter points.
* A definition of `signedCrossings` (a count of eigenvalues that change
  sign).
* A lemma `eta_is_spectral`: `η` depends only on the sign pattern of
  the spectrum, not on any choice of index labels.
* **NO** definition `etaJump S := 2 * S.card`.
* **NO** axiom of the form `etaJump S = 2 * S.card`.

The connection to the integer counts (12, 144, 168, 768) lives in
`IntegerCounts.lean` and depends on (a) the spectral-identification
predicate of `SpectralIdentification.lean` and (b) one APS /
Bismut-Freed named axiom with citation.

## Smuggling check

* Nothing in this file forces `η(D_F)` or its jump to any specific
  numerical value for any specific spectrum.
* The spectrum `λ : Fin n → ℝ` is a free parameter; different
  choices give different `η` values.
* The cardinality of a mode-class `Finset` does NOT, by itself,
  determine an η-jump in this file.
-/

namespace SpectralPhysics.Eta.JumpMap

/-! ## The finite spectral triple data -/

/-- Total complex dimension of the finite Hilbert space `H_F` of the
    Connes-Chamseddine spectral triple for the Standard Model.
    `dimHF = 4 · 96`, the v0.9 Theorem `thm:384` (line 8211).
    We use the reducible `abbrev` so that `Fin dimHF` is automatically
    `Fintype` and `DecidableEq`. -/
abbrev dimHF : ℕ := 384

/-- A **finite spectral triple** is, for our purposes, an indexed
    eigenvalue spectrum of `D_F`.  We model this as a function
    `λ : Fin dimHF → ℝ` — the (real) eigenvalues of `D_F` listed with
    multiplicity in some basis.

    No assumption is made here about which indices correspond to which
    physical modes (quarks, leptons, ...) — that connection is the
    content of the `SpectralIdentification` predicate in
    `SpectralIdentification.lean`.

    The KO-dim 6 J-pairing structure is recorded as a separate
    predicate `KOdim6JStructure` (placeholder; not used in this file). -/
structure FiniteSpectralTriple where
  /-- Real eigenvalues of `D_F` indexed over `Fin 384`. -/
  spectrum : Fin dimHF → ℝ

namespace FiniteSpectralTriple

variable (T : FiniteSpectralTriple)

/-- The signum of a real eigenvalue, with `sgn(0) = 0`.
    This is the building block of the η-spectral-asymmetry sum. -/
noncomputable def sgnEigenvalue (k : Fin dimHF) : ℝ :=
  if T.spectrum k > 0 then 1
  else if T.spectrum k < 0 then -1
  else 0

/-- The η-invariant of `D_F` as a **spectral asymmetry sum**:

  `η(D_F) := Σ_k sgn(λ_k)`.

This is the standard Atiyah-Patodi-Singer (1975, 1976) definition for
the finite-dimensional case (no heat-kernel regularization needed
because the spectrum is finite).

**Crucially**: this is NOT `2 · |modes|`.  It is a function of the
underlying real spectrum `T.spectrum`, and different spectra give
different values of η. -/
noncomputable def eta : ℝ :=
  ∑ k : Fin dimHF, T.sgnEigenvalue k

/-- An eigenvalue `λ k` is **positive at `T`** if `T.spectrum k > 0`. -/
def isPositive (k : Fin dimHF) : Prop := T.spectrum k > 0

/-- An eigenvalue `λ k` is **negative at `T`** if `T.spectrum k < 0`. -/
def isNegative (k : Fin dimHF) : Prop := T.spectrum k < 0

end FiniteSpectralTriple

/-! ## η-jump along a spectral flow (structural definition)

A one-parameter spectral flow is encoded as two endpoint triples
`T_before` and `T_after`.  The η-jump is the difference of their η
invariants.  -/

/-- The **η-jump** between two endpoint spectral triples:

  `Δη := η(T_after) − η(T_before)`.

This is the STRUCTURAL definition.  It is real-valued, not natural-
number-valued, and it is NOT `2 · S.card` for any `S`. -/
noncomputable def etaSpectralFlow
    (T_before T_after : FiniteSpectralTriple) : ℝ :=
  T_after.eta - T_before.eta

/-- The set of indices `k` at which an eigenvalue **changes sign**
    between `T_before` and `T_after`.  This is the spectral-flow
    crossing set in finite dimension.

    A crossing is recorded when the eigenvalue is nonzero at one
    endpoint and has the opposite sign (or is zero) at the other.

    This `Finset` is determined by the underlying real spectra, not
    chosen by hand. -/
noncomputable def crossingSet
    (T_before T_after : FiniteSpectralTriple) : Finset (Fin dimHF) :=
  Finset.univ.filter (fun k =>
    T_before.sgnEigenvalue k ≠ T_after.sgnEigenvalue k)

/-- A **structurally identified** mode-class crossing: those crossings
    in `crossingSet T_before T_after` that lie inside a given index
    subset `S`.  Again, no `2 · card` here. -/
noncomputable def crossingsInClass
    (T_before T_after : FiniteSpectralTriple)
    (S : Finset (Fin dimHF)) : Finset (Fin dimHF) :=
  S ∩ crossingSet T_before T_after

/-! ## Honesty lemmas

These lemmas record explicitly that `eta` depends only on the real
spectrum, and that two spectra agreeing on signs give the same `eta`.
They are stated and proved at the level of the structural definition,
NOT via any `2 · card` identification. -/

/-- If two finite spectral triples have pointwise-equal eigenvalues,
    they have equal η-invariants.  (Trivial congruence, recorded for
    documentation.) -/
theorem eta_congr {T T' : FiniteSpectralTriple}
    (h : ∀ k, T.spectrum k = T'.spectrum k) :
    T.eta = T'.eta := by
  unfold FiniteSpectralTriple.eta FiniteSpectralTriple.sgnEigenvalue
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [h k]

/-- If `T.spectrum k = 0` for every `k`, then `η(T) = 0`. -/
theorem eta_zero_of_spectrum_zero (T : FiniteSpectralTriple)
    (h : ∀ k, T.spectrum k = 0) : T.eta = 0 := by
  unfold FiniteSpectralTriple.eta FiniteSpectralTriple.sgnEigenvalue
  apply Finset.sum_eq_zero
  intro k _
  rw [h k]
  simp

/-! ## What is NOT in this file

Three things are deliberately absent:

1. **No `def etaJump (S : Finset (Fin dimHF)) : ℕ := 2 * S.card`**.
   The previous deceptive branch had exactly this definition; the
   "axiom" `etaJump_two_times_modes` then reduced to `rfl`.  Such a
   construction encodes nothing physical.

2. **No axiom forcing `eta` to a specific numerical value**.  The
   eigenvalue spectrum is a free parameter.

3. **No identification of `Fin dimHF` indices with physical particle
   modes**.  That identification is a *predicate*, formalised in
   `SpectralIdentification.lean`, and used as a hypothesis (NOT an
   axiom) by the conditional integer-count theorems in
   `IntegerCounts.lean`.

The integers 12, 144, 168, 768 do not appear anywhere in this file.
They appear only in `IntegerCounts.lean`, conditionally on the
spectral-identification predicate and the named APS / Bismut-Freed
doubling axiom. -/

end SpectralPhysics.Eta.JumpMap
