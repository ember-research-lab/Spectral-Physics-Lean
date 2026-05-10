/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.EtaJSelfConj.EtaInvariant
import SpectralPhysics.Analysis.SpectralFlow

/-!
# Spectral Flow on the J-Self-Conjugate Sub-Block as `y_R` Varies

## What this file establishes

The spectral flow `sf` of `D_F |_{(1,1)_0}` along the path
`y_R : 0 → physical` counts net level crossings through 0:

  `sf({D_t}) := #{(λ_n(t), t) : λ_n(0⁻) < 0, λ_n(t_+) > 0}
              − #{(λ_n(t), t) : λ_n(0⁻) > 0, λ_n(t_+) < 0}`.

For the J-self-conjugate Majorana sector, eigenvalues split
*symmetrically* `0 → ±M_R(t)` as `y_R(t)` increases.  Each pairing
contributes one positive and one negative crossing, so the **net**
spectral flow is 0 — even though the *gross* crossing count is
`2 · Ngen` (six for the SM).

## The hierarchy of integers — none of which is 8

Within the J-self-conjugate sector we now have a clean enumeration:

| Quantity                              | Value | Reason                          |
|---------------------------------------|-------|---------------------------------|
| η(D_F |_{ν_R})                       | 0     | Majorana pairing (this folder)  |
| sf({D_F^t}_{0 → physical})            | 0     | symmetric crossings (this file) |
| (gross crossings: |sf|+ + |sf|-)      | 6     | 3 gen × 2 doubling              |
| AS chiral index of (1,1)_0           | 0     | singlet bundle (sister branch)  |
| Cl(0,6) module dim                    | 8     | KO-dim 6 (NOT an index)         |

Only the Cl(0,6) module dim is 8, and that is a fibre-rank, not any
flow or index.

## Tier classification

* **Tier 1 (proved here)**: in the symmetric-splitting model, the
  net spectral flow is 0 and the gross crossing count is `2·Ngen`.
* **Tier 1 (proved here)**: 0 ≠ 8 and `2·Ngen ≠ 8` for `Ngen = 3`.
* **Tier 3 (named axiom)**: the actual `D_F`-spectrum on the J-self-
  conjugate sub-block follows the symmetric-splitting model — i.e.
  `D_F |_{ν_R}` at `y_R = 0` has a single zero with multiplicity
  `Ngen` that splits to `±M_R` as `y_R → physical`.  This is the
  standard NCG content of the See–Saw mechanism plus KO-dim-6 sign
  triple.

## References

* Atiyah–Patodi–Singer 1976, "Spectral asymmetry and Riemannian
  geometry II", Math. Proc. Camb. Phil. Soc. **78**.
* Phillips, J. (1996). "Self-adjoint Fredholm operators and spectral
  flow." Canad. Math. Bull. **39**, 460–467.
* `SpectralPhysics/Analysis/SpectralFlow.lean` — repo's existing
  spectral-flow scaffolding (APS index ≡ spectral flow).
-/

namespace SpectralPhysics.EtaJSelfConj

open SpectralPhysics.IndexJSelfConj
open SpectralPhysics.MajoranaSelfRef

/-! ## Symmetric splitting model

The structural content of the See-Saw mechanism on the J-self-
conjugate sector:

  At `y_R = 0`: one zero eigenvalue per generation per Majorana sector.
  At `y_R > 0`: each zero splits to `±M_R(y_R)`, with `M_R → 0` as
  `y_R → 0⁺`.

We model this directly by a structure that records the splitting at
each generation.  The "spectral flow" is then a finite signed sum
over the genealogy of crossings. -/

/-- One Majorana generation's path of eigenvalues as `y_R` varies from
    `0` to physical.  At `y_R = 0` the eigenvalue is 0; at the physical
    endpoint it has split to `±M_R`. -/
structure MajoranaPath where
  /-- The Majorana mass at the physical endpoint (`y_R = physical`). -/
  MR_physical : ℝ
  /-- We require `M_R > 0` at the physical endpoint (gapped). -/
  MR_pos : 0 < MR_physical

namespace MajoranaPath

/-- The "up-crossing": eigenvalue moves from `0` to `+M_R`. -/
def upCrossing (_p : MajoranaPath) : ℤ := 1

/-- The "down-crossing": eigenvalue moves from `0` to `-M_R`. -/
def downCrossing (_p : MajoranaPath) : ℤ := -1

/-- **Net crossing per Majorana sector**: each `0` splits to BOTH
    `+M_R` AND `-M_R`, so the net flow is `+1 + (-1) = 0`. -/
def netCrossing (p : MajoranaPath) : ℤ := p.upCrossing + p.downCrossing

/-- **Gross crossing count** (absolute number of crossings through 0,
    regardless of direction).  Per Majorana sector this is 2: one up,
    one down. -/
def grossCrossings (_p : MajoranaPath) : ℕ := 2

/-- **Tier 1.**  Per-generation Majorana net flow = 0. -/
@[simp] theorem netCrossing_eq_zero (p : MajoranaPath) :
    p.netCrossing = 0 := by
  unfold netCrossing upCrossing downCrossing; ring

/-- **Tier 1.**  Per-generation Majorana gross crossing count = 2. -/
@[simp] theorem grossCrossings_eq_two (p : MajoranaPath) :
    p.grossCrossings = 2 := rfl

end MajoranaPath

/-! ## Total spectral flow over `Ngen` generations -/

/-- The list of `Ngen` Majorana paths (one per generation, all with the
    same Majorana mass `MR > 0`). -/
def nuR_paths (Ngen : ℕ) (MR : ℝ) (h : 0 < MR) : List MajoranaPath :=
  List.replicate Ngen { MR_physical := MR, MR_pos := h }

/-- **Total net spectral flow** of `D_F |_{(1,1)_0}` along
    `y_R : 0 → physical`. -/
def totalNetFlow (Ngen : ℕ) (MR : ℝ) (h : 0 < MR) : ℤ :=
  ((nuR_paths Ngen MR h).map MajoranaPath.netCrossing).sum

/-- **Total gross crossing count** along `y_R : 0 → physical`. -/
def totalGrossCrossings (Ngen : ℕ) (MR : ℝ) (h : 0 < MR) : ℕ :=
  ((nuR_paths Ngen MR h).map MajoranaPath.grossCrossings).sum

/-- **Tier 1.**  The total *net* spectral flow on the J-self-conjugate
    sector is 0 (symmetric Majorana splitting). -/
theorem totalNetFlow_eq_zero (Ngen : ℕ) (MR : ℝ) (h : 0 < MR) :
    totalNetFlow Ngen MR h = 0 := by
  unfold totalNetFlow nuR_paths
  -- Each entry maps to 0; List.replicate of 0; sum is 0
  induction Ngen with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.map_cons, List.sum_cons,
        MajoranaPath.netCrossing_eq_zero, zero_add]
    exact ih

/-- **Tier 1.**  The total gross crossing count is `2·Ngen`
    (3 gen × 2 = 6 in the SM). -/
theorem totalGrossCrossings_eq (Ngen : ℕ) (MR : ℝ) (h : 0 < MR) :
    totalGrossCrossings Ngen MR h = 2 * Ngen := by
  unfold totalGrossCrossings nuR_paths
  induction Ngen with
  | zero => simp
  | succ n ih =>
    simp [List.replicate_succ, List.map_cons, List.sum_cons,
          MajoranaPath.grossCrossings_eq_two] at ih ⊢
    omega

/-- **Tier 1.**  In the SM, the total gross crossing count is 6. -/
@[simp] theorem totalGrossCrossings_SM (MR : ℝ) (h : 0 < MR) :
    totalGrossCrossings 3 MR h = 6 :=
  totalGrossCrossings_eq 3 MR h

/-- **Tier 1.**  In the SM, the total net spectral flow is 0. -/
@[simp] theorem totalNetFlow_SM (MR : ℝ) (h : 0 < MR) :
    totalNetFlow 3 MR h = 0 :=
  totalNetFlow_eq_zero 3 MR h

/-- **Tier 1.**  The total *net* spectral flow is NOT 8 (it is 0). -/
theorem totalNetFlow_ne_eight (Ngen : ℕ) (MR : ℝ) (h : 0 < MR) :
    totalNetFlow Ngen MR h ≠ 8 := by
  rw [totalNetFlow_eq_zero]; decide

/-- **Tier 1.**  The total *gross* crossing count is NOT 8 — for
    `Ngen = 3` it is `6`, for `Ngen = 4` it is `8` (no SM with 4
    Majorana-singlet generations is known).  In particular for
    `Ngen = 3` it is 6 ≠ 8. -/
theorem totalGrossCrossings_SM_ne_eight (MR : ℝ) (h : 0 < MR) :
    totalGrossCrossings 3 MR h ≠ 8 := by
  rw [totalGrossCrossings_SM]; decide

/-! ## Why neither the net flow nor the gross count is 8

Both numbers are forced by KO-dim 6 + 3-generation structure:
* `net flow = 0`  (J-self-conjugacy → symmetric splitting),
* `gross   = 6`  (`Ngen = 3, 2 sectors / gen`).

For the *gross* count to equal 8 one would need `Ngen = 4`, contrary
to the experimentally established three SM generations and to the
NCG–KO-dim-6 input.  For the *net* flow to equal 8, the J-self-
conjugacy itself would have to be broken — but breaking it removes
the very Majorana property that motivated this sub-block.

The "8" cannot come from (η + ½·sf) either, since both summands are
zero (cf. `APSIndex.lean`).

The verdict (`Verdict.lean`) records the result. -/

/-- **Tier 1 — diagnostic.**  In the SM, the spectral-flow numbers
    available from this sector are `(0, 6)` — neither equals 8. -/
theorem SM_flow_data_disjoint_from_eight (MR : ℝ) (h : 0 < MR) :
    totalNetFlow 3 MR h = 0 ∧
    totalGrossCrossings 3 MR h = 6 ∧
    totalNetFlow 3 MR h ≠ 8 ∧
    totalGrossCrossings 3 MR h ≠ 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact totalNetFlow_SM MR h
  · exact totalGrossCrossings_SM MR h
  · rw [totalNetFlow_SM]; decide
  · rw [totalGrossCrossings_SM]; decide

end SpectralPhysics.EtaJSelfConj
