/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.YukawaHierarchy.Bundle.PrincipalBundle
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# The 't Hooft Symbols η^a_{μν}

The 't Hooft symbols are the structure constants of the SU(2) BPST instanton
construction. As real-valued antisymmetric matrices indexed by `a ∈ Fin 3`,
`μ, ν ∈ Fin 4`:

  `η^a_{ij} = ε_{aij}`        for `i, j ∈ {0, 1, 2}`  (3D Levi-Civita)
  `η^a_{i4} = δ_{ai}`         for `i ∈ {0, 1, 2}`
  `η^a_{4i} = -δ_{ai}`         for `i ∈ {0, 1, 2}`
  `η^a_{44} = 0`

(Index 4 is `Fin 4` index `3` in Lean.)

## Tier classification

* **Tier 1 (proved)**: antisymmetry in `(μ, ν)`; `Σ_{μν} (η^a_{μν})² = 4`
  for each `a`; `Σ_{a,μ,ν} (η^a_{μν})² = 12`.
* **Tier 1 (proved)**: self-duality `η^a_{μν} = (1/2) ε_{μνρσ} η^a_{ρσ}`
  (proved by `decide` over the 3 × 6 × 6 = 108 cases).

## References

* 't Hooft, G. (1976). "Computation of the quantum effects due to a
  four-dimensional pseudoparticle." Phys. Rev. D 14, 3432.
* Coleman, S. (1985). *Aspects of Symmetry*, Chapter 7.
-/

namespace SpectralPhysics.YukawaHierarchy.Bundle

/-! ## 3D Levi-Civita (auxiliary) -/

/-- The 3-dimensional Levi-Civita symbol `ε_{ijk}` valued in `ℤ`. -/
def epsilon3 (i j k : Fin 3) : ℤ :=
  if i = 0 ∧ j = 1 ∧ k = 2 then  1
  else if i = 1 ∧ j = 2 ∧ k = 0 then  1
  else if i = 2 ∧ j = 0 ∧ k = 1 then  1
  else if i = 0 ∧ j = 2 ∧ k = 1 then -1
  else if i = 2 ∧ j = 1 ∧ k = 0 then -1
  else if i = 1 ∧ j = 0 ∧ k = 2 then -1
  else 0

@[simp] theorem epsilon3_012 : epsilon3 0 1 2 = 1 := rfl
@[simp] theorem epsilon3_120 : epsilon3 1 2 0 = 1 := rfl
@[simp] theorem epsilon3_201 : epsilon3 2 0 1 = 1 := rfl
@[simp] theorem epsilon3_021 : epsilon3 0 2 1 = -1 := rfl
@[simp] theorem epsilon3_210 : epsilon3 2 1 0 = -1 := rfl
@[simp] theorem epsilon3_102 : epsilon3 1 0 2 = -1 := rfl

/-- ε_{ijk} = -ε_{jik}: antisymmetric in first two. -/
theorem epsilon3_antisym_12 (i j k : Fin 3) :
    epsilon3 i j k = -epsilon3 j i k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

/-! ## The 't Hooft symbols (self-dual variant) -/

/-- The self-dual 't Hooft symbol `η^a_{μν} : Fin 3 → Fin 4 → Fin 4 → ℤ`.

    Concretely (in 0-indexed Fin 4):
      η^a_{ij} = ε_{aij}      for i, j < 3
      η^a_{i3} = δ_{ai}       for i < 3
      η^a_{3i} = -δ_{ai}       for i < 3
      η^a_{33} = 0
      η^a_{ii} = 0  (any i)
-/
def tHooftEta (a : Fin 3) (μ ν : Fin 4) : ℤ :=
  -- Case 1: both μ and ν in {0, 1, 2} → 3D Levi-Civita ε_{aμν}
  if hμ : μ.val < 3 then
    if hν : ν.val < 3 then
      epsilon3 a ⟨μ.val, hμ⟩ ⟨ν.val, hν⟩
    else
      -- ν = 3 case: η^a_{i3} = δ_{ai}
      if a.val = μ.val then 1 else 0
  else  -- μ = 3
    if ν.val < 3 then
      -- η^a_{3i} = -δ_{ai}
      if a.val = ν.val then -1 else 0
    else
      0  -- μ = ν = 3

/-! ## Properties of the η symbol -/

/-- Antisymmetry: `η^a_{μν} = -η^a_{νμ}`. -/
theorem tHooftEta_antisym (a : Fin 3) (μ ν : Fin 4) :
    tHooftEta a μ ν = -tHooftEta a ν μ := by
  fin_cases a <;> fin_cases μ <;> fin_cases ν <;> rfl

/-- Diagonal vanishes: `η^a_{μμ} = 0`. -/
theorem tHooftEta_diag (a : Fin 3) (μ : Fin 4) :
    tHooftEta a μ μ = 0 := by
  have h : tHooftEta a μ μ = -tHooftEta a μ μ := tHooftEta_antisym a μ μ
  linarith

/-- Some specific values for sanity. -/
@[simp] theorem tHooftEta_0_1_2 : tHooftEta 0 1 2 = 1 := rfl
@[simp] theorem tHooftEta_0_2_1 : tHooftEta 0 2 1 = -1 := rfl
@[simp] theorem tHooftEta_0_0_3 : tHooftEta 0 0 3 = 1 := rfl
@[simp] theorem tHooftEta_0_3_0 : tHooftEta 0 3 0 = -1 := rfl
@[simp] theorem tHooftEta_1_1_3 : tHooftEta 1 1 3 = 1 := rfl
@[simp] theorem tHooftEta_2_2_3 : tHooftEta 2 2 3 = 1 := rfl

/-- The squared sum over `(μ, ν)` for fixed `a`:

      `Σ_{μ, ν} (η^a_{μν})² = 4`

    (4 nonzero entries each equal to ±1: from `ε_{a··}` 2 entries and
    from `δ_{a·}` 2 entries (one in each of the 4-th row/column)). -/
theorem tHooftEta_sumsq_per_a (a : Fin 3) :
    (∑ μ : Fin 4, ∑ ν : Fin 4, (tHooftEta a μ ν)^2) = 4 := by
  fin_cases a <;> rfl

/-- Total squared sum over all `(a, μ, ν)`:

      `Σ_{a, μ, ν} (η^a_{μν})² = 12`. -/
theorem tHooftEta_total_sumsq :
    (∑ a : Fin 3, ∑ μ : Fin 4, ∑ ν : Fin 4, (tHooftEta a μ ν)^2) = 12 := by
  decide

/-! ## 4D Levi-Civita (auxiliary, for self-duality) -/

/-- A specific 4-tuple is even iff it's a positive permutation of `(0,1,2,3)`. -/
def isEvenPerm4 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Prop := fun μ ν ρ σ =>
    (μ = 0 ∧ ν = 1 ∧ ρ = 2 ∧ σ = 3)
  ∨ (μ = 0 ∧ ν = 2 ∧ ρ = 3 ∧ σ = 1)
  ∨ (μ = 0 ∧ ν = 3 ∧ ρ = 1 ∧ σ = 2)
  ∨ (μ = 1 ∧ ν = 0 ∧ ρ = 3 ∧ σ = 2)
  ∨ (μ = 1 ∧ ν = 2 ∧ ρ = 0 ∧ σ = 3)
  ∨ (μ = 1 ∧ ν = 3 ∧ ρ = 2 ∧ σ = 0)
  ∨ (μ = 2 ∧ ν = 0 ∧ ρ = 1 ∧ σ = 3)
  ∨ (μ = 2 ∧ ν = 1 ∧ ρ = 3 ∧ σ = 0)
  ∨ (μ = 2 ∧ ν = 3 ∧ ρ = 0 ∧ σ = 1)
  ∨ (μ = 3 ∧ ν = 0 ∧ ρ = 2 ∧ σ = 1)
  ∨ (μ = 3 ∧ ν = 1 ∧ ρ = 0 ∧ σ = 2)
  ∨ (μ = 3 ∧ ν = 2 ∧ ρ = 1 ∧ σ = 0)

/-- A specific 4-tuple is odd iff it's an odd permutation of `(0,1,2,3)`. -/
def isOddPerm4 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Prop := fun μ ν ρ σ =>
    (μ = 0 ∧ ν = 1 ∧ ρ = 3 ∧ σ = 2)
  ∨ (μ = 0 ∧ ν = 2 ∧ ρ = 1 ∧ σ = 3)
  ∨ (μ = 0 ∧ ν = 3 ∧ ρ = 2 ∧ σ = 1)
  ∨ (μ = 1 ∧ ν = 0 ∧ ρ = 2 ∧ σ = 3)
  ∨ (μ = 1 ∧ ν = 2 ∧ ρ = 3 ∧ σ = 0)
  ∨ (μ = 1 ∧ ν = 3 ∧ ρ = 0 ∧ σ = 2)
  ∨ (μ = 2 ∧ ν = 0 ∧ ρ = 3 ∧ σ = 1)
  ∨ (μ = 2 ∧ ν = 1 ∧ ρ = 0 ∧ σ = 3)
  ∨ (μ = 2 ∧ ν = 3 ∧ ρ = 1 ∧ σ = 0)
  ∨ (μ = 3 ∧ ν = 0 ∧ ρ = 1 ∧ σ = 2)
  ∨ (μ = 3 ∧ ν = 1 ∧ ρ = 2 ∧ σ = 0)
  ∨ (μ = 3 ∧ ν = 2 ∧ ρ = 0 ∧ σ = 1)

/-- The 4D Levi-Civita symbol `ε_{μνρσ}` valued in `ℤ`.
    Encoded by case analysis (24 + 24 + many zeros = 256 cases). -/
def epsilon4 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℤ := fun μ ν ρ σ =>
  -- Even permutations of (0,1,2,3) → +1
  if μ = 0 ∧ ν = 1 ∧ ρ = 2 ∧ σ = 3 then 1
  else if μ = 0 ∧ ν = 2 ∧ ρ = 3 ∧ σ = 1 then 1
  else if μ = 0 ∧ ν = 3 ∧ ρ = 1 ∧ σ = 2 then 1
  else if μ = 1 ∧ ν = 0 ∧ ρ = 3 ∧ σ = 2 then 1
  else if μ = 1 ∧ ν = 2 ∧ ρ = 0 ∧ σ = 3 then 1
  else if μ = 1 ∧ ν = 3 ∧ ρ = 2 ∧ σ = 0 then 1
  else if μ = 2 ∧ ν = 0 ∧ ρ = 1 ∧ σ = 3 then 1
  else if μ = 2 ∧ ν = 1 ∧ ρ = 3 ∧ σ = 0 then 1
  else if μ = 2 ∧ ν = 3 ∧ ρ = 0 ∧ σ = 1 then 1
  else if μ = 3 ∧ ν = 0 ∧ ρ = 2 ∧ σ = 1 then 1
  else if μ = 3 ∧ ν = 1 ∧ ρ = 0 ∧ σ = 2 then 1
  else if μ = 3 ∧ ν = 2 ∧ ρ = 1 ∧ σ = 0 then 1
  -- Odd permutations of (0,1,2,3) → -1
  else if μ = 0 ∧ ν = 1 ∧ ρ = 3 ∧ σ = 2 then -1
  else if μ = 0 ∧ ν = 2 ∧ ρ = 1 ∧ σ = 3 then -1
  else if μ = 0 ∧ ν = 3 ∧ ρ = 2 ∧ σ = 1 then -1
  else if μ = 1 ∧ ν = 0 ∧ ρ = 2 ∧ σ = 3 then -1
  else if μ = 1 ∧ ν = 2 ∧ ρ = 3 ∧ σ = 0 then -1
  else if μ = 1 ∧ ν = 3 ∧ ρ = 0 ∧ σ = 2 then -1
  else if μ = 2 ∧ ν = 0 ∧ ρ = 3 ∧ σ = 1 then -1
  else if μ = 2 ∧ ν = 1 ∧ ρ = 0 ∧ σ = 3 then -1
  else if μ = 2 ∧ ν = 3 ∧ ρ = 1 ∧ σ = 0 then -1
  else if μ = 3 ∧ ν = 0 ∧ ρ = 1 ∧ σ = 2 then -1
  else if μ = 3 ∧ ν = 1 ∧ ρ = 2 ∧ σ = 0 then -1
  else if μ = 3 ∧ ν = 2 ∧ ρ = 0 ∧ σ = 1 then -1
  else 0  -- repeated indices

/-- ε_{0123} = 1. -/
@[simp] theorem epsilon4_0123 : epsilon4 0 1 2 3 = 1 := rfl

/-- ε is antisymmetric in the first two indices. -/
theorem epsilon4_swap_12 (μ ν ρ σ : Fin 4) :
    epsilon4 μ ν ρ σ = -epsilon4 ν μ ρ σ := by
  fin_cases μ <;> fin_cases ν <;> fin_cases ρ <;> fin_cases σ <;> rfl

/-! ## Self-duality of the 't Hooft symbol -/

/-- **Tier 1.**  The self-duality identity:

      `2 · η^a_{μν} = Σ_{ρ,σ} ε_{μνρσ} · η^a_{ρσ}`.

    This is the defining property of the SELF-DUAL 't Hooft symbol.
    Proved by `decide` over the 3 × 4 × 4 = 48 cases of `(a, μ, ν)`. -/
theorem tHooftEta_selfDual (a : Fin 3) (μ ν : Fin 4) :
    (∑ ρ : Fin 4, ∑ σ : Fin 4, epsilon4 μ ν ρ σ * tHooftEta a ρ σ)
      = 2 * tHooftEta a μ ν := by
  fin_cases a <;> fin_cases μ <;> fin_cases ν <;> rfl

end SpectralPhysics.YukawaHierarchy.Bundle
