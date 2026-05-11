/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Multiset.Bind
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Spectral Operations (Honest Scaffolding)

Defines `Spectrum` (= `Multiset ℝ`) and three candidate binary
operations: `additiveConv`, `multiplicativeConv`, and a
`freeConv` placeholder.  See `STATUS.md` and the file docstring
on `FreeFails.lean` for the placeholder's honest scope.

## References

* Reed-Simon I, §VIII.10 (additive lift)
* Voiculescu (1985); Hurwitz (1898)
-/

namespace SpectralPhysics.CompositionUniqueness

/-- A spectrum is a finite multiset of real eigenvalues. -/
abbrev Spectrum : Type := Multiset ℝ

namespace Spectrum

/-- The trace of a spectrum is the sum of its eigenvalues. -/
def trace (μ : Spectrum) : ℝ := μ.sum

/-- A spectrum is **non-trivial** if it has at least one element. -/
def NonTrivial (μ : Spectrum) : Prop := Multiset.card μ ≠ 0

@[simp] lemma trace_zero : trace (0 : Spectrum) = 0 := by
  unfold trace; simp

@[simp] lemma trace_singleton (a : ℝ) : trace ({a} : Multiset ℝ) = a := by
  unfold trace; simp

end Spectrum

/-- **Additive convolution**: the spectrum of `H_A ⊗ I + I ⊗ H_B`. -/
def additiveConv (μ ν : Spectrum) : Spectrum :=
  μ.bind (fun a => ν.map (fun b => a + b))

/-- **Multiplicative convolution**: the spectrum of `H_A ⊗ H_B`. -/
def multiplicativeConv (μ ν : Spectrum) : Spectrum :=
  μ.bind (fun a => ν.map (fun b => a * b))

/-- **Free convolution placeholder** — deliberate stand-in. -/
def freeConv (_ _ : Spectrum) : Spectrum := (0 : Spectrum)

/-! ## Auxiliary sum lemmas for translated multisets -/

private lemma sum_map_add_left (a : ℝ) (ν : Spectrum) :
    (ν.map (fun b => a + b)).sum = (Multiset.card ν : ℝ) * a + ν.sum := by
  induction ν using Multiset.induction_on with
  | empty => simp
  | cons b ν ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.sum_cons,
          Multiset.card_cons]
      push_cast
      ring

private lemma sum_map_mul_left (a : ℝ) (ν : Spectrum) :
    (ν.map (fun b => a * b)).sum = a * ν.sum := by
  induction ν using Multiset.induction_on with
  | empty => simp
  | cons b ν ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.sum_cons]
      ring

private lemma sum_map_affine (μ ν : Spectrum) :
    (μ.map (fun a : ℝ => (Multiset.card ν : ℝ) * a + ν.sum)).sum =
      (Multiset.card ν : ℝ) * μ.sum +
        (Multiset.card μ : ℝ) * ν.sum := by
  induction μ using Multiset.induction_on with
  | empty => simp
  | cons a μ ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.sum_cons,
          Multiset.card_cons]
      push_cast
      ring

private lemma sum_map_scale (μ : Spectrum) (S : ℝ) :
    (μ.map (fun a : ℝ => a * S)).sum = μ.sum * S := by
  induction μ using Multiset.induction_on with
  | empty => simp
  | cons a μ ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.sum_cons]
      ring

/-! ## Cardinality identities for the two genuine operations -/

@[simp] lemma card_additiveConv (μ ν : Spectrum) :
    Multiset.card (additiveConv μ ν) = Multiset.card μ * Multiset.card ν := by
  unfold additiveConv
  rw [Multiset.card_bind]
  simp only [Function.comp]
  have heq : (μ.map fun a => Multiset.card (ν.map (fun b => a + b))) =
              μ.map (fun _ => Multiset.card ν) := by
    apply Multiset.map_congr rfl
    intro a _; simp
  rw [heq, Multiset.map_const', Multiset.sum_replicate]
  simp

@[simp] lemma card_multiplicativeConv (μ ν : Spectrum) :
    Multiset.card (multiplicativeConv μ ν) =
      Multiset.card μ * Multiset.card ν := by
  unfold multiplicativeConv
  rw [Multiset.card_bind]
  simp only [Function.comp]
  have heq : (μ.map fun a => Multiset.card (ν.map (fun b => a * b))) =
              μ.map (fun _ => Multiset.card ν) := by
    apply Multiset.map_congr rfl
    intro a _; simp
  rw [heq, Multiset.map_const', Multiset.sum_replicate]
  simp

/-! ## Trace identities for the two genuine operations -/

lemma trace_additiveConv (μ ν : Spectrum) :
    Spectrum.trace (additiveConv μ ν) =
      (Multiset.card ν : ℝ) * Spectrum.trace μ +
        (Multiset.card μ : ℝ) * Spectrum.trace ν := by
  unfold additiveConv Spectrum.trace
  rw [Multiset.sum_bind]
  have eq1 : (μ.map fun a => (ν.map (fun b => a + b)).sum) =
              μ.map (fun a => (Multiset.card ν : ℝ) * a + ν.sum) := by
    apply Multiset.map_congr rfl
    intro a _; exact sum_map_add_left a ν
  rw [eq1]
  exact sum_map_affine μ ν

lemma trace_multiplicativeConv (μ ν : Spectrum) :
    Spectrum.trace (multiplicativeConv μ ν) =
      Spectrum.trace μ * Spectrum.trace ν := by
  unfold multiplicativeConv Spectrum.trace
  rw [Multiset.sum_bind]
  have eq1 : (μ.map fun a => (ν.map (fun b => a * b)).sum) =
              μ.map (fun a => a * ν.sum) := by
    apply Multiset.map_congr rfl
    intro a _; exact sum_map_mul_left a ν
  rw [eq1]
  exact sum_map_scale μ ν.sum

end SpectralPhysics.CompositionUniqueness
