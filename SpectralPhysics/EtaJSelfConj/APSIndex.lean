/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.EtaJSelfConj.EtaInvariant
import SpectralPhysics.EtaJSelfConj.SpectralFlow
import SpectralPhysics.IndexJSelfConj.IndexComputation

/-!
# APS-style Combined Index for the J-Self-Conjugate Sub-Block

## What this file computes

The Atiyah–Patodi–Singer index theorem for a Dirac operator on a
manifold with boundary, applied to the cylinder version of the
twisted `D_F`, takes the form

  `index_APS(D) = ∫_M Â(M) ∧ ch(E)  −  ½ (η(D|_∂M) + dim ker D|_∂M)`

(Atiyah–Patodi–Singer 1975, equation (4.3) of Part I.)

We assemble the three pieces for the J-self-conjugate sub-block:

| Piece                                            | Value | File              |
|--------------------------------------------------|-------|-------------------|
| Bulk: `∫ Â · ch(E_{ν_R})` on `S^4`               | 0     | IndexJSelfConj    |
| Boundary η: `η(D_F|_{ν_R})`                      | 0     | EtaInvariant      |
| Boundary kernel: `dim ker D_F|_{ν_R}` at y_R = 0 | Ngen  | SpectralFlow      |
| **Composite APS index**                          | -Ngen/2 |                  |

For `Ngen = 3`: `index_APS = 0 - ½(0 + 3) = -3/2` — not even an
integer, let alone 8.  (The non-integrality is itself diagnostic:
the APS formula assumes the Dirac operator is *invertible* on the
boundary, i.e. `dim ker = 0`; allowing `dim ker > 0` produces the
half-integer correction.)

If we instead use the alternative APS variant with `½ dim ker`
absorbed into a τ-correction, one still has

  `index_APS = 0 - 0 - τ(0)`,

where `τ(0) = (½ dim ker)` for the trivial-spectrum case.  Either
way: not 8.

We compute the candidate APS index `(η + sf)/2` separately (the
"Bismut–Freed pairing") and show it equals 0.

## Tier classification

* **Tier 1 (proved here)**: `(η + sf)/2 = 0` for the J-self-
  conjugate sub-block, every `Ngen`, every `MR > 0`.
* **Tier 1 (proved here)**: this 0 is not 8.
* **Tier 1 (proved here)**: the boundary-kernel APS combination
  `(η + dim ker)/2 = Ngen/2` is `3/2` in the SM, also not 8.
* **Tier 3 (named axioms)**: APS 1975, Bismut–Freed 1986.

## References

* Atiyah–Patodi–Singer 1975 (Part I), equation (4.3).
* Atiyah–Patodi–Singer 1976 (Part II), Theorem (3.10).
* Bismut, Freed (1986). "The analysis of elliptic families II."
  CMP **107**, 103–163.
* `SpectralPhysics/Analysis/SpectralFlow.lean` — the repo's local
  spectral-flow infrastructure (theorem `eta_from_spectral_flow`).
-/

namespace SpectralPhysics.EtaJSelfConj

open SpectralPhysics.IndexJSelfConj
open SpectralPhysics.MajoranaSelfRef

/-! ## The Bismut–Freed combination `(η + sf)/2`

Bismut–Freed (1986) showed that for a smooth path of self-adjoint
Dirac operators `D_t`, the change in the η-invariant equals twice
the spectral flow:

    `η(D_1) - η(D_0) = 2 · sf({D_t})`

(this is the local form of `eta_from_spectral_flow` in
`Analysis/SpectralFlow.lean`).

For the J-self-conjugate sector, BOTH `η(D_t) = 0` for every `t`
(Majorana pairing — `EtaInvariant.lean`) AND `sf({D_t}) = 0`
(symmetric splitting — `SpectralFlow.lean`).  So the change in η
is consistent: `0 - 0 = 2·0`. -/

/-- The candidate **Bismut–Freed APS pairing** for the J-self-
    conjugate sector along `y_R : 0 → physical`.

    Formally `(η_final + 2·sf)/2`.  We use the SF expression `2·sf`
    rather than `½·sf` to keep the integer/integer-half pairing
    aligned with `eta_from_spectral_flow`. -/
noncomputable def APS_pairing_majorana (Ngen : ℕ) (MR : ℝ) (h : 0 < MR) : ℝ :=
  (nuR_spectrum Ngen MR h).etaInvariant
    + 2 * (totalNetFlow Ngen MR h : ℝ)

/-- **Tier 1.**  The Bismut–Freed APS pairing on the J-self-
    conjugate sector is identically 0. -/
theorem APS_pairing_majorana_eq_zero
    (Ngen : ℕ) (MR : ℝ) (h : 0 < MR) :
    APS_pairing_majorana Ngen MR h = 0 := by
  unfold APS_pairing_majorana
  rw [nuR_etaInvariant_eq_zero, totalNetFlow_eq_zero]
  norm_num

/-- **Tier 1.**  The APS pairing is NOT 8. -/
theorem APS_pairing_majorana_ne_eight
    (Ngen : ℕ) (MR : ℝ) (h : 0 < MR) :
    APS_pairing_majorana Ngen MR h ≠ 8 := by
  rw [APS_pairing_majorana_eq_zero]
  norm_num

/-! ## The full APS bulk-plus-boundary index for `D_F |_{ν_R}`

In the cylinder model with `M = S^4 × [0,1]` and the J-self-
conjugate boundary data, the APS theorem reads

  `index_APS = ∫_{S^4} Â · ch(ν_R bundle) - (η_{boundary} + h_{boundary})/2`

where `h_{boundary} = dim ker D_∂` is the kernel dimension at the
boundary (= `Ngen` in the SM at `y_R = 0`).

For `M = S^4` and ν_R singlet:
* `∫_{S^4} Â = 0` (`AhatGenus_S4 = 0`).
* `ch(ν_R) = rank = 1` (singlet, so just constant 1).
* The bulk is `∫ 0 · 1 = 0`.

For the boundary at `y_R = physical`:
* `η = 0` (Majorana pairing),
* `h = 0` (gapped),
so the boundary correction is 0.

For the boundary at `y_R = 0`:
* `η = 0` (still Majorana-paired),
* `h = Ngen` (one zero mode per generation, = 3 in the SM),
giving boundary correction `−Ngen/2 = −3/2`.

Either way the bulk vanishes and the boundary gives 0 or `−3/2`,
both of which are ≠ 8. -/

/-- The bulk integral on `S^4` for the J-self-conjugate sub-rep.
    Equal to `AS_index_jsc 1 = 0` (the AS index already integrates
    `Â · ch`). -/
def bulk_S4 (ν : ℤ) : ℤ := AS_index_jsc ν

/-- **Tier 1.**  The bulk integral on `S^4` is 0 for any ν. -/
@[simp] theorem bulk_S4_eq_zero (ν : ℤ) : bulk_S4 ν = 0 :=
  AS_index_jsc_eq_zero ν

/-- The dimension of the boundary kernel of `D_F|_{ν_R}` at `y_R = 0`
    (one zero mode per generation, before the y_R-mass splits the
    spectrum).  This is `Ngen` in the SM. -/
def boundaryKernelDim_y_R_zero (Ngen : ℕ) : ℕ := Ngen

/-- **Tier 1.**  The boundary kernel dim at `y_R = 0` is 3 in the SM. -/
@[simp] theorem boundaryKernelDim_SM :
    boundaryKernelDim_y_R_zero 3 = 3 := rfl

/-- The full APS index at the `y_R = 0` boundary:

      `index_APS_y_R_zero = bulk - (η + h)/2 = 0 - (0 + Ngen)/2 = -Ngen/2`. -/
noncomputable def APS_index_y_R_zero (Ngen : ℕ) (ν : ℤ) (MR : ℝ) (h : 0 < MR) : ℝ :=
  (bulk_S4 ν : ℝ)
    - ((nuR_spectrum Ngen MR h).etaInvariant
       + (boundaryKernelDim_y_R_zero Ngen : ℝ)) / 2

/-- **Tier 1.**  At the `y_R = 0` boundary, the APS index is `-Ngen/2`. -/
theorem APS_index_y_R_zero_eq
    (Ngen : ℕ) (ν : ℤ) (MR : ℝ) (h : 0 < MR) :
    APS_index_y_R_zero Ngen ν MR h = -((Ngen : ℝ) / 2) := by
  unfold APS_index_y_R_zero
  rw [bulk_S4_eq_zero, nuR_etaInvariant_eq_zero,
      boundaryKernelDim_y_R_zero]
  push_cast
  ring

/-- **Tier 1.**  In the SM, the y_R = 0 APS index is `-3/2`. -/
@[simp] theorem APS_index_SM_y_R_zero (MR : ℝ) (h : 0 < MR) :
    APS_index_y_R_zero 3 1 MR h = -(3 / 2) := by
  rw [APS_index_y_R_zero_eq]
  push_cast
  ring

/-- **Tier 1.**  The y_R = 0 APS index is NOT 8 (it is a half-integer). -/
theorem APS_index_y_R_zero_ne_eight
    (Ngen : ℕ) (ν : ℤ) (MR : ℝ) (h : 0 < MR) (hN : 0 < Ngen) :
    APS_index_y_R_zero Ngen ν MR h ≠ 8 := by
  rw [APS_index_y_R_zero_eq]
  -- -(Ngen/2) = 8 ↔ Ngen = -16, impossible since Ngen > 0
  intro heq
  -- heq : -(Ngen / 2) = 8.  Multiply by -2: Ngen = -16.
  have hpos : (0 : ℝ) < (Ngen : ℝ) := by exact_mod_cast hN
  linarith

/-- The full APS index at the `y_R = physical` boundary:

      `index_APS_y_R_physical = bulk - (η + h)/2 = 0 - (0 + 0)/2 = 0`. -/
noncomputable def APS_index_y_R_physical (Ngen : ℕ) (ν : ℤ) (MR : ℝ) (h : 0 < MR) : ℝ :=
  (bulk_S4 ν : ℝ)
    - ((nuR_spectrum Ngen MR h).etaInvariant + 0) / 2

/-- **Tier 1.**  At the physical boundary, APS index = 0. -/
theorem APS_index_y_R_physical_eq_zero
    (Ngen : ℕ) (ν : ℤ) (MR : ℝ) (h : 0 < MR) :
    APS_index_y_R_physical Ngen ν MR h = 0 := by
  unfold APS_index_y_R_physical
  rw [bulk_S4_eq_zero, nuR_etaInvariant_eq_zero]
  norm_num

/-- **Tier 1.**  Physical-boundary APS index is NOT 8. -/
theorem APS_index_y_R_physical_ne_eight
    (Ngen : ℕ) (ν : ℤ) (MR : ℝ) (h : 0 < MR) :
    APS_index_y_R_physical Ngen ν MR h ≠ 8 := by
  rw [APS_index_y_R_physical_eq_zero]
  norm_num

/-! ## The combined verdict — neither boundary delivers an 8 -/

/-- **Tier 1 — combined verdict.**  Across both natural choices of
    APS boundary data (`y_R = 0` and `y_R = physical`), the J-self-
    conjugate sector's APS index is

    * `−Ngen/2` at `y_R = 0` (= `−3/2` for SM),
    * `0`      at `y_R = physical`.

    Neither equals 8. -/
theorem APS_full_combined_ne_eight (MR : ℝ) (h : 0 < MR) :
    APS_index_y_R_zero 3 1 MR h ≠ 8 ∧
    APS_index_y_R_physical 3 1 MR h ≠ 8 ∧
    APS_pairing_majorana 3 MR h ≠ 8 := by
  refine ⟨?_, ?_, ?_⟩
  · exact APS_index_y_R_zero_ne_eight 3 1 MR h (by decide)
  · exact APS_index_y_R_physical_ne_eight 3 1 MR h
  · exact APS_pairing_majorana_ne_eight 3 MR h

end SpectralPhysics.EtaJSelfConj
