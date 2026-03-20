/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Axiom 1: Relational Foundation

Reality is a relational structure (X, μ, k), where:
- X is a finite set
- μ : X → ℝ₊ is a measure (positive weights)
- k : X × X → ℂ is a Hermitian kernel: k(x,y) = conj(k(y,x))

This file defines relational structures and their basic properties.

## References

* Ben-Shalom, "Spectral Physics", Chapter 1, Axiom 1
-/

/-- A relational structure: the fundamental object of spectral physics.

A relational structure consists of a finite set X with a positive measure μ
and a Hermitian kernel k. The kernel encodes the "relations" between elements
of X: |k(x,y)| is the strength and arg(k(x,y)) is the phase. -/
structure RelationalStructure where
  /-- The carrier set -/
  X : Type*
  /-- Finiteness -/
  [fin : Fintype X]
  /-- Decidable equality on X -/
  [deceq : DecidableEq X]
  /-- The measure: positive weight on each point -/
  μ : X → ℝ
  /-- Positivity of the measure -/
  μ_pos : ∀ x, 0 < μ x
  /-- The Hermitian kernel: the relation between pairs -/
  k : X → X → ℂ
  /-- Hermitian symmetry: k(x,y) = conj(k(y,x)) -/
  k_hermitian : ∀ x y, k x y = starRingEnd ℂ (k y x)

namespace RelationalStructure

attribute [instance] RelationalStructure.fin RelationalStructure.deceq

variable (S : RelationalStructure)

/-- The modulus of the kernel: the strength of the relation -/
noncomputable def kernelModulus (x y : S.X) : ℝ := ‖S.k x y‖

/-- The phase of the kernel: the gauge content -/
noncomputable def kernelPhase (x y : S.X) : ℝ := Complex.arg (S.k x y)

/-- Hermitian symmetry implies the modulus is symmetric -/
theorem kernelModulus_symm (x y : S.X) :
    S.kernelModulus x y = S.kernelModulus y x := by
  simp only [kernelModulus]
  rw [S.k_hermitian x y, Complex.norm_conj]

/-- Hermitian symmetry implies the phase is antisymmetric
    (for kernels not on the negative real axis) -/
theorem kernelPhase_antisymm (x y : S.X)
    (h : Complex.arg (S.k y x) ≠ Real.pi) :
    S.kernelPhase x y = -S.kernelPhase y x := by
  simp only [kernelPhase]
  rw [S.k_hermitian x y, Complex.arg_conj, if_neg h]

/-- When the kernel is real and non-negative, the structure is classical
(a weighted graph). -/
def isClassical : Prop :=
  ∀ x y, (S.k x y).im = 0 ∧ 0 ≤ (S.k x y).re

/-- Two points are related if the kernel is nonzero -/
def related (x y : S.X) : Prop := S.k x y ≠ 0

/-- The degree of a point: sum of kernel moduli -/
noncomputable def degree (x : S.X) : ℝ :=
  ∑ y : S.X, S.kernelModulus x y * S.μ y

/-- A relational structure is connected if every pair of points is
related by a chain of nonzero kernel entries -/
def isConnected : Prop :=
  ∀ x y : S.X, x ≠ y →
    ∃ (path : List S.X),
      path.head? = some x ∧ path.getLast? = some y ∧
      ∀ i, ∀ h : i + 1 < path.length,
        S.related (path.get ⟨i, by omega⟩) (path.get ⟨i + 1, h⟩)

end RelationalStructure
