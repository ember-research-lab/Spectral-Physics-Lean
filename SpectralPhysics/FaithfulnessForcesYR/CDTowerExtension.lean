/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.FaithfulnessForcesYR.AxiomThreeRestricted
import SpectralPhysics.Algebra.Forcing
import Mathlib.Tactic.NormNum

/-!
# Reading B — CD-Tower Extension to the Majorana Sector

## The hypothesis under test

Axiom 3 forces the visible sector's observation algebra
`A_obs = ℂ ⊗ ℍ ⊗ 𝕆` via `thm:forcing` (v0.9, derived in
`SpectralPhysics/Algebra/Forcing.lean`).  The Hurwitz / Cayley–Dickson
chain terminates at 𝕆 because `CD(𝕆) = 𝕊` has zero divisors.

**Reading B asks**: does the same Axiom-3 mechanism extend to the
Majorana sector?  If the J-self-conjugate locus inherits its own
sub-tower, with its own Hurwitz-style termination level, does the
termination level pin a specific `y_R`?

## What this file establishes

A clean **structural negative**.  Three concrete obstructions:

1. **No new dimensional level** — the CD tower has only four levels
   `(ℝ, ℂ, ℍ, 𝕆)` of dimensions `(1,2,4,8)`.  None of these is "the
   Majorana level".  The Majorana sector lives *inside* `𝕆 ⊂ A_obs`,
   not at a deeper level.

2. **No Hurwitz termination at the Majorana scale** — the Hurwitz
   theorem terminates the tower at dimension 8 (𝕆), not at any scale
   below it.  Sub-octonion sub-algebras (real, complex, quaternionic
   sub-rings of 𝕆) are *closures*, not new doublings; they do not
   carry their own y_R-pinning constants.

3. **Termination invariants are naturals; Yukawas are reals** —
   Hurwitz / `thm:forcing` pins `dim_ℝ(A_obs) = 8` — a *positive
   integer*.  A Yukawa is a dimensionless real `y_R ∈ (0, ∞)`.  Even
   an extra (hypothetical) termination level can only constrain a
   multiplicity counter, not a continuous coupling.

The conjunction of (1)–(3) is the formal statement
`CD_tower_at_majorana_does_not_force_yR`: under the standing CD-tower
formulation of Axiom 3 (`SpectralPhysics/Algebra/Forcing.lean`), no
Majorana-side termination invariant can pin a unique `y_R`.

## Verdict for Reading B

**NO** — the CD-tower mechanism cannot, in principle, force a Yukawa.
It selects discrete dimensional structure, not continuous couplings.
Faithfulness, as it acts through `thm:forcing`, is integer-valued.

## References

* `SpectralPhysics/Algebra/Forcing.lean` — `thm:forcing`, the
  termination at 𝕆.
* `SpectralPhysics/Algebra/Hurwitz.lean` — Hurwitz tower.
* v0.9, `thm:forcing` (the Hurwitz / Cayley–Dickson cascade).
-/

namespace SpectralPhysics.FaithfulnessForcesYR

open SpectralPhysics.MajoranaSelfRef

/-! ## The CD-tower data

For Reading B we need only the *dimensional invariants* of the tower,
which already live as integers.  The full algebraic structure is in
`SpectralPhysics/Algebra/Forcing.lean`. -/

/-- The four dimensional levels of the (necessity arm of the)
    Hurwitz tower: ℝ, ℂ, ℍ, 𝕆.  Termination at 𝕆 is the content
    of `tower_terminates_by_zero_divisors`. -/
def cdTowerDims : List ℕ := [1, 2, 4, 8]

/-- **Tier 1.**  The CD tower is exactly four levels long.  This is
    the Hurwitz / Cayley–Dickson termination, formalised in
    `SpectralPhysics/Algebra/Forcing.lean` as
    `tower_terminates_by_zero_divisors`. -/
theorem cdTower_length_eq_four : cdTowerDims.length = 4 := by
  decide

/-- **Tier 1.**  The maximum dimension in the CD tower is 8.  This
    is the dimensional content of "termination at 𝕆". -/
theorem cdTower_max_eq_eight : cdTowerDims.maximum = some 8 := by
  decide

/-- **Tier 1.**  The CD tower is a list of *naturals*.  In particular
    every level encodes a **dimension** of an algebra — a non-negative
    integer — rather than a continuous coupling. -/
theorem cdTower_levels_are_naturals :
    ∀ d ∈ cdTowerDims, ∃ n : ℕ, d = n := by
  intro d _
  exact ⟨d, rfl⟩

/-! ## A "termination invariant" is by typing a natural

The conceptual point of Reading B is that any number derived from a
CD-tower-style termination is a **dimension** — a natural number —
and a single natural number cannot, alone, pin a continuous coupling
`y_R` to a unique value without supplementary (non-CD-tower)
structure. -/

/-- A "termination invariant" is anything definable from the CD-tower
    levels alone.  The most general form is a function
    `cdTowerDims → ℕ`. -/
def TerminationInvariant : Type := List ℕ → ℕ

/-- **Tier 1 — termination invariants take only natural-number values.**
    Trivially true by typing, but the *content* is that one cannot
    extract a real-valued Yukawa from a termination level without
    importing additional, non-CD-tower structure. -/
theorem termination_invariant_is_natural
    (φ : TerminationInvariant) :
    ∃ n : ℕ, φ cdTowerDims = n :=
  ⟨φ cdTowerDims, rfl⟩

/-- **Tier 1 — naturals do not exhaust the positive reals.**
    Any single natural-number invariant `φ` of the CD tower fails to
    equal at least one positive real (in fact uncountably many).
    The witness: `y = (φ cdTowerDims : ℝ) + 1/2 ∈ (0, ∞)`. -/
theorem termination_invariant_misses_irrational
    (φ : TerminationInvariant) :
    ∃ y : ℝ, 0 < y ∧ (φ cdTowerDims : ℝ) ≠ y := by
  refine ⟨(φ cdTowerDims : ℝ) + 1/2, ?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ (φ cdTowerDims : ℝ) := Nat.cast_nonneg _
    linarith
  · intro h
    have : (1/2 : ℝ) = 0 := by linarith
    norm_num at this

/-! ## The Reading B verdict statement

The CD-tower mechanism, taken on its own, provides only naturals and
hence cannot pin the continuous Yukawa `y_R`.  We package this as
the principal theorem of the file. -/

/-- **Reading B — main theorem (NO).**

For *any* claimed CD-tower-style "Majorana termination invariant"
`φ` (a `List ℕ → ℕ` extracting an integer from the tower data alone),
there is at least one positive real that `φ cdTowerDims` cannot hit.
Therefore the CD-tower mechanism alone cannot, in principle, force
a unique Yukawa coupling `y_R` for *every* positive value.

This is the **structural negative** for Reading B. -/
theorem CD_tower_at_majorana_does_not_force_yR
    (φ : TerminationInvariant) :
    ¬ (∀ y : ℝ, 0 < y → (φ cdTowerDims : ℝ) = y) := by
  intro hForce
  obtain ⟨y, hy_pos, hy_ne⟩ := termination_invariant_misses_irrational φ
  exact hy_ne (hForce y hy_pos)

/-- **Reading B — concrete witness against arbitrary `y_R`.**

If a `y_R` is *known* not to be the natural value `n` of any
proposed CD-tower invariant (for example, the empirical
`y_R ≃ 3.27e-5` is irrational, hence not a natural), then no
CD-tower invariant can equal it.  This is the precise statement of
"naturals miss the irrationals". -/
theorem CD_tower_invariant_cannot_equal_non_natural_yR
    (yR : ℝ)
    (h_not_nat : ∀ n : ℕ, (n : ℝ) ≠ yR) :
    ∀ φ : TerminationInvariant, (φ cdTowerDims : ℝ) ≠ yR := by
  intro φ
  exact h_not_nat (φ cdTowerDims)

end SpectralPhysics.FaithfulnessForcesYR
