/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Cutoff Family — Λ-Indexed Family of Self-Adjoint Operators

The v0.9 manuscript's `prop:spectral-convergence` (line 1437) is the
**spectral analogue of the universality hypothesis in statistical
mechanics**: the low-eigenvalue spectrum of the family `D_F(Λ)`
indexed by an ultraviolet cutoff `Λ ∈ (0, ∞)` converges, in a suitable
sense, as `Λ → ∞`, **independent of UV details**.

This file carries the *substrate*:

* `CutoffFamily` — a structure abstracting "Λ ↦ self-adjoint operator
  whose low-eigenvalue spectrum is what we care about." We do not
  formalise self-adjointness on a Hilbert space in Mathlib here; the
  spectrum is exposed via a numeric `eigenvalue` projection.
* `IsRegulatorFamily` — a named `Prop` predicate carrying the
  v0.9 standing assumptions on the family (in particular, that
  `Λ ≥ Λ_IR` makes the family well-behaved at low energies).

## Honest scope

* The "operator" is **not** an abstract self-adjoint operator on a
  Hilbert space. We model the spectral data we actually use: the
  eigenvalue sequence `n ↦ λ_n(Λ)` and the cutoff scale `Λ_IR`
  below which the family is not asked to make low-energy sense.
* The Λ → ∞ limit is not a Mathlib `Filter.Tendsto` of operators; the
  *substantive convergence* is captured at the
  `LowEigenvalueRestriction` level, on truncated spectral data.
* The family must be **non-trivial in Λ**: a *constant* family
  `D_F(Λ) := D_F_fixed` trivially makes every universality statement
  hold. We forbid that by predicate (see `IsNonTrivialFamily`).

## References

* Ben-Shalom (2026). *Spectral Physics* v0.9, line 1437,
  `prop:spectral-convergence`.
* Kato, T. (1995). *Perturbation Theory for Linear Operators.*
  Classics in Mathematics, Springer. §V (Stability theorems for
  self-adjoint operators).
* Reed, M. and Simon, B. (1978). *Methods of Modern Mathematical
  Physics IV: Analysis of Operators.* Academic Press. Ch. XIII
  (Spectral analysis), §XIII.5 (trace-class and Schatten ideals).
* Wilson, K.G. (1971). *Renormalization group and critical phenomena.*
  Phys. Rev. B **4**, 3174; Phys. Rev. D **3**, 1818. — UV/IR
  separation in statistical mechanics.
-/

namespace SpectralPhysics.IRUVScaleSeparation

/-! ## The cutoff family substrate -/

/-- A **cutoff family** is, abstractly,

  * a positive lower-cutoff `Λ_IR > 0` (the IR scale below which
    low-energy observables are well-defined);
  * a Λ-indexed assignment of an eigenvalue sequence `D_F`
    representing the spectrum of `D_F(Λ)`. The first argument is
    `Λ ∈ ℝ`, the second is `n ∈ ℕ` indexing the eigenvalues.

  We require eigenvalues to be non-negative (the framework's `D_F²`
  is positive semidefinite by self-adjointness of `D_F`).

  No assumption is placed here on Λ-dependence beyond
  positivity. The substantive UV-suppression rate enters
  `KatoStability.lean` as a predicate. -/
structure CutoffFamily where
  /-- IR scale: below this, the family is not asked to make
      low-energy sense. -/
  Λ_IR : ℝ
  /-- Positivity of the IR scale. -/
  Λ_IR_pos : 0 < Λ_IR
  /-- Eigenvalue assignment: `D_F Λ n` is the `n`-th non-negative
      eigenvalue of `D_F(Λ)`. -/
  D_F : ℝ → ℕ → ℝ
  /-- Non-negativity of eigenvalues (the framework's `D_F²ge 0`). -/
  D_F_nonneg : ∀ (Λ : ℝ) (n : ℕ), Λ_IR ≤ Λ → 0 ≤ D_F Λ n

namespace CutoffFamily

/-- Convenience: the IR scale of a family is non-negative. -/
theorem Λ_IR_nonneg (R : CutoffFamily) : 0 ≤ R.Λ_IR :=
  le_of_lt R.Λ_IR_pos

end CutoffFamily

/-! ## The v0.9 standing axioms on the family (predicate form)

This is the predicate-hypothesis form of v0.9's "regulator family"
assumptions. We expose three substantive contents:

1. **Low-energy stability** — for any pair `Λ ≤ Λ'` with
   `Λ_IR ≤ Λ`, the low eigenvalues at cutoffs `Λ` and `Λ'`
   agree at some chosen scale `μ`. This is the IR/UV separation.
2. **Λ-monotonicity of high modes** — added later in
   `KatoStability` as a Schatten-norm bound.
3. **Non-triviality** — Λ-dependence is non-trivial below a
   chosen scale (rules out `D_F R Λ := constant`).
-/

/-- **Non-trivial Λ-dependence.**  The family `D_F R` is not the
    constant function in `Λ`. Spelled out: there exist `Λ`, `Λ'` and
    an `n` such that the `n`-th eigenvalue genuinely differs.

    This is the *anti-trivialization* predicate: without it,
    `D_F R Λ := D_F_fixed` makes every universality statement hold
    vacuously (anti-pattern explicitly forbidden by the
    audit-discipline rules).

    Note that an honest `CutoffFamily` arising from physics is
    *always* non-trivial in `Λ` (else `Λ` plays no role). We carry
    it as a predicate to make the requirement explicit in the
    universality theorems. -/
def IsNonTrivialFamily (R : CutoffFamily) : Prop :=
  ∃ (Λ Λ' : ℝ) (n : ℕ), R.Λ_IR ≤ Λ ∧ R.Λ_IR ≤ Λ' ∧ R.D_F Λ n ≠ R.D_F Λ' n

/-- **The v0.9 regulator-family axioms.**  Predicate form. A
    `CutoffFamily R` is a *regulator family* iff:

    * the family is non-trivial in `Λ` (rules out the constant
      anti-pattern);
    * the IR scale is finite (carried by `R.Λ_IR_pos`);
    * the high-frequency modes are controlled — this content is
      *deferred* to `KatoStability`'s Schatten-norm predicate.

    This is the predicate-hypothesis form of v0.9's *standing
    assumption* on the spectral family. We do **not** axiomatize
    "every `CutoffFamily` is a regulator family" — that is exactly
    what makes spectral universality conditional, not free. -/
def IsRegulatorFamily (R : CutoffFamily) : Prop :=
  IsNonTrivialFamily R

/-- The constant family `D_F(Λ) := λ ↦ 0` is **not** a regulator
    family. This rules out the audit-forbidden anti-pattern. -/
theorem constant_family_not_regulator
    (Λ_IR : ℝ) (hΛ : 0 < Λ_IR) :
    let R : CutoffFamily :=
      { Λ_IR := Λ_IR
        Λ_IR_pos := hΛ
        D_F := fun _ _ => 0
        D_F_nonneg := fun _ _ _ => le_refl 0 }
    ¬ IsRegulatorFamily R := by
  intro R
  unfold IsRegulatorFamily IsNonTrivialFamily
  rintro ⟨_, _, _, _, _, h_ne⟩
  exact h_ne rfl

end SpectralPhysics.IRUVScaleSeparation
