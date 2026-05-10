/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Defs

/-!
# J-Fixed Locus of the Finite Spectral Triple

## Hypothesis under test

The Self-Model Deficit theorem
`−ζ̃'_vis(0) = dim(H_hid) = 288` runs over the *full* visible
spectrum of `D_F` (48 modes, multiplicity-weighted).  We test the
**restriction to the J-fixed locus**:

  `Fix(J) := { ψ ∈ H_F : J ψ = ψ }`,

asking whether the restricted ζ-sum reduces to a single-eigenvalue
equation `(structural quantity) = −ln y_R`.

This file establishes the **structural locus** itself: which sub-reps
of the SO(10) 16 lie inside `Fix(J)`, and what the spectral
multiplicity of that locus is under standard NCG vs. a non-standard
"J-quotient" reading.

## What is proved here (Tier 1)

* `is_J_fixed` predicate on a sub-rep, equivalent to
  `J-self-conjugate` (color singlet, weak singlet, Y = 0).
* The locus is **non-empty** and equals the ν_R sub-rep
  `(1, 1)_0` only.
* Under **standard NCG (Connes–Marcolli §17.5)**, the spectral
  multiplicity of `Fix(J) ⊂ H_F` is `6 = 3 generations × 2 (Dirac
  particle/antiparticle doubling)`.
* Under the **non-standard J-quotient reading** (Hypothesis A;
  v0.9 single-mode), the multiplicity collapses to `1`.
* These two readings are arithmetically distinct: `6 ≠ 1`.

## What this file does NOT decide

Whether standard NCG or the J-quotient reading is correct — that's
the verdict of `RestrictedZeta.lean` and `Verdict.lean`.

## References

* Connes, A. (1996), *Gravity coupled with matter and the foundation
  of noncommutative geometry*, CMP **182**, 155–176.
* Connes, A. & Marcolli, M. (2008), *Noncommutative Geometry, Quantum
  Fields and Motives*, AMS Coll. Pub. **55**, §15.4 and §17.5.
* van Suijlekom, W. (2015), *Noncommutative Geometry and Particle
  Physics*, Springer, Theorem 5.5.7.
* Sibling branches:
  - `compute/majorana-self-reference`,
    `SpectralPhysics/MajoranaSelfRef/JSelfConjugate.lean`.
  - `compute/atiyah-singer-J-self-conj`,
    `SpectralPhysics/IndexJSelfConj/JSelfConjBlock.lean`.
  - `compute/majorana-block-residue`,
    `SpectralPhysics/MajoranaBlock/Discriminator.lean` —
    this branch reuses its multiplicity discriminator.
-/

namespace SpectralPhysics.SelfModelJFixed

/-! ## Sub-rep data (parallel to MajoranaSelfRef.GaugeRep) -/

/-- An SO(10) 16 sub-rep, labelled by its `(SU(3), SU(2))_Y` quantum
    numbers. -/
structure SubRep where
  dimColor : ℕ
  dimWeak  : ℕ
  hyperch  : ℚ
  deriving DecidableEq, Repr

namespace SubRep

/-- A sub-rep is **J-fixed** iff it satisfies `R̄ = R`: color singlet,
    weak singlet, zero hypercharge.  This is the spectral content of
    `J ψ = ψ` (rather than `J ψ = ψ_c` with `ψ_c ≠ ψ`).

    Connes-Marcolli (2008) §15.4 derives this as the criterion for
    a `J`-self-conjugate component of the matter rep. -/
def is_J_fixed (R : SubRep) : Prop :=
  R.dimColor = 1 ∧ R.dimWeak = 1 ∧ R.hyperch = 0

instance (R : SubRep) : Decidable (is_J_fixed R) := by
  unfold is_J_fixed; infer_instance

end SubRep

/-! ## The six sub-reps of the SO(10) 16 -/

/-- Q_L = `(3, 2)_{1/6}`. -/
def repQ_L : SubRep := ⟨3, 2, 1/6⟩
/-- u_R^c = `(3̄, 1)_{-2/3}`. -/
def repU_Rc : SubRep := ⟨3, 1, -2/3⟩
/-- d_R^c = `(3̄, 1)_{1/3}`. -/
def repD_Rc : SubRep := ⟨3, 1, 1/3⟩
/-- L_L = `(1, 2)_{-1/2}`. -/
def repL_L : SubRep := ⟨1, 2, -1/2⟩
/-- e_R^c = `(1, 1)_{1}`. -/
def repE_Rc : SubRep := ⟨1, 1, 1⟩
/-- ν_R = `(1, 1)_{0}`. -/
def repNu_R : SubRep := ⟨1, 1, 0⟩

/-! ## Selection theorems (parallel to MajoranaSelfRef) -/

/-- ν_R is J-fixed. -/
theorem repNu_R_is_J_fixed : SubRep.is_J_fixed repNu_R := by
  refine ⟨rfl, rfl, rfl⟩

/-- Q_L is NOT J-fixed (color = 3). -/
theorem repQ_L_not_J_fixed : ¬ SubRep.is_J_fixed repQ_L := by
  intro ⟨h, _, _⟩; exact absurd h (by decide)

/-- u_R^c is NOT J-fixed (color = 3). -/
theorem repU_Rc_not_J_fixed : ¬ SubRep.is_J_fixed repU_Rc := by
  intro ⟨h, _, _⟩; exact absurd h (by decide)

/-- d_R^c is NOT J-fixed (color = 3). -/
theorem repD_Rc_not_J_fixed : ¬ SubRep.is_J_fixed repD_Rc := by
  intro ⟨h, _, _⟩; exact absurd h (by decide)

/-- L_L is NOT J-fixed (Y = -1/2 ≠ 0). -/
theorem repL_L_not_J_fixed : ¬ SubRep.is_J_fixed repL_L := by
  intro ⟨_, _, h⟩
  have hy : (repL_L.hyperch : ℚ) = -1/2 := rfl
  rw [hy] at h
  exact absurd h (by norm_num)

/-- e_R^c is NOT J-fixed (Y = 1 ≠ 0). -/
theorem repE_Rc_not_J_fixed : ¬ SubRep.is_J_fixed repE_Rc := by
  intro ⟨_, _, h⟩
  have hy : (repE_Rc.hyperch : ℚ) = 1 := rfl
  rw [hy] at h
  exact absurd h (by norm_num)

/-- **Headline (Tier 1) — uniqueness of the J-fixed locus inside 16.**

    Among the six sub-reps of the SO(10) 16, ν_R = (1,1)_0 is the
    UNIQUE J-fixed component.  This locates the J-fixed locus
    structurally; the spectral multiplicity is the next question. -/
theorem nu_R_unique_J_fixed_in_16 :
    SubRep.is_J_fixed repNu_R ∧
    ¬ SubRep.is_J_fixed repQ_L ∧
    ¬ SubRep.is_J_fixed repU_Rc ∧
    ¬ SubRep.is_J_fixed repD_Rc ∧
    ¬ SubRep.is_J_fixed repL_L ∧
    ¬ SubRep.is_J_fixed repE_Rc :=
  ⟨repNu_R_is_J_fixed, repQ_L_not_J_fixed, repU_Rc_not_J_fixed,
   repD_Rc_not_J_fixed, repL_L_not_J_fixed, repE_Rc_not_J_fixed⟩

/-! ## Spectral multiplicity of the J-fixed locus

There are TWO distinct counts:

1. **Standard NCG (Connes–Marcolli §17.5)**: the J-fixed locus
   inherits the full Dirac multiplicity of its sub-rep.  ν_R has
   3 generations × 2 (particle/antiparticle) = `6` modes in
   `H_F`.  The Majorana mass insertion is treated by *extending*
   `D_F` to a 4×4 block, preserving the multiplicity count of the
   underlying degree of freedom.

2. **Non-standard J-quotient reading (Hypothesis A; v0.9 single-
   mode)**: the J-fixed locus is *quotiented* by the J-action,
   collapsing the Majorana doubling, and giving a single
   flavor-blind eigenvalue.  This is the multiplicity-1 reading.

These are recorded as definitional integers and distinguished
arithmetically. -/

/-- Number of generations. -/
def Ngen : ℕ := 3

/-- Dirac particle/antiparticle doubling. -/
def diracDouble : ℕ := 2

/-- **Standard NCG multiplicity** of the J-fixed locus
    `Fix(J) ⊂ H_F`.

    `mult_std = Ngen × diracDouble = 6`.

    Citation: Connes–Marcolli (2008) §17.5, Theorem 1.214; this is
    the "extend `D_F` to 4×4" construction.  See also
    `compute/majorana-block-residue` `mult_B = 6`. -/
def mult_std : ℕ := Ngen * diracDouble

/-- **Non-standard J-quotient multiplicity** of the J-fixed locus.

    `mult_quot = 1`.

    Citation: Hypothesis A in `compute/majorana-block-residue`;
    `pre_geometric/baker_selects_yR/verdict.md`.  This reading
    treats the J-action as a halving operation and the (1,1)_0
    block as a flavor-diagonal scalar. -/
def mult_quot : ℕ := 1

/-- **Tier 1.**  The standard multiplicity is 6. -/
theorem mult_std_eq_six : mult_std = 6 := by
  unfold mult_std Ngen diracDouble; decide

/-- **Tier 1.**  The J-quotient multiplicity is 1. -/
theorem mult_quot_eq_one : mult_quot = 1 := rfl

/-- **Tier 1 — the multiplicity discriminator.**  The two readings
    give arithmetically distinct multiplicities. -/
theorem mult_std_ne_quot : mult_std ≠ mult_quot := by
  rw [mult_std_eq_six, mult_quot_eq_one]; decide

/-! ## Cardinality of the J-fixed locus as a set of modes

The J-fixed locus is exhausted by ν_R — but it carries *some*
spectral content (multiplicity > 0) in both readings.  The
question is which integer.

In particular it is NOT degenerate (multiplicity 0); the locus
*does* have spectral content. -/

/-- **Tier 1.**  The J-fixed locus is non-empty: ν_R lies in it. -/
theorem J_fixed_nonempty :
    ∃ R : SubRep, SubRep.is_J_fixed R := ⟨repNu_R, repNu_R_is_J_fixed⟩

/-- **Tier 1.**  In both readings, the J-fixed locus has positive
    spectral multiplicity.  This rules out the DEGENERATE verdict
    (the route is not vacuous). -/
theorem J_fixed_mult_positive_std : 0 < mult_std := by
  rw [mult_std_eq_six]; decide

theorem J_fixed_mult_positive_quot : 0 < mult_quot := by
  rw [mult_quot_eq_one]; decide

end SpectralPhysics.SelfModelJFixed
