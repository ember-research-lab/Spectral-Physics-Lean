/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.YukawaHierarchy.CharmTauRatio

/-!
# The Instanton-Counting Interpretation of `3/16`

The framework's claim `r_c/r_τ = 3/16 = N_c / dim(16)` admits a topological
reformulation:

      `y_c / y_τ = ν_total / dim(16)`

where `ν_total` is the total topological charge (instanton number) of the
SU(3)_c bundle on the manifold-side of the spectral triple. The numerical
identification `ν_total = 3` matches the **number of generations**, since
each generation contributes one unit of color winding to the SU(3) bundle.

Equivalently, `3/16 = N_c · ν_per_gen / dim(16)` with `ν_per_gen = 1`.

## Why this is "the right form"

* Counting `N_c` (which equals 3 in QCD) is rep-theoretic — fixed once
  you choose SU(3) as the color group.
* Counting `ν_total = N_gen` (which equals 3 in the SM) is topological —
  fixed once you choose the gauge bundle on the spacetime side.
* The product `N_c · ν_per_gen / dim(16)` is a pure topological-cum-
  representation-theoretic invariant.

The numerical coincidence that `N_c = N_gen = 3` makes the two readings
of the "3" in 3/16 indistinguishable empirically. They have **different
physical content** in the framework.

## Tier classification

* **Tier 1** (proved): the algebraic identity
  `N_c · ν / dim(16) = (3 ν) / 16` for ν ∈ ℕ.
* **Tier 3** (open): that the SM bundle has `ν_total = 3` (one instanton
  per generation), AND that this topological choice forces the Yukawa
  ratio. Both halves are conjectures.

## References

* Atiyah-Singer index theorem (1968) — basic input for the index in
  representation R: `index(D_R) = ν · T_2(R) / T_2(fund)`.
* For SU(3) BPST instanton in the SO(10) 16-rep:
  the 16 decomposes as 2(3) ⊕ 2(3̄) ⊕ 4(1) under SU(3); per generation
  k = 1 instanton gives 2 negative-chirality + 2 positive-chirality
  zero modes (anomaly-free).
-/

namespace SpectralPhysics.YukawaHierarchy

/-! ## The instanton-counting ratio -/

/-- The structural ratio `N_c · ν / dim(16)`. -/
def instantonRatio (ν : ℕ) : ℚ := (Nc : ℚ) * (ν : ℚ) / (dimSpinor16 : ℚ)

/-- For one instanton (ν = 1): `N_c / dim(16) = 3 / 16`. -/
@[simp] theorem instantonRatio_one :
    instantonRatio 1 = 3 / 16 := by
  simp [instantonRatio, Nc, dimSpinor16, totalStates_eq_sixteen]

/-- For three instantons (ν = 3): `3 N_c / dim(16) = 9 / 16`. -/
@[simp] theorem instantonRatio_three :
    instantonRatio 3 = 9 / 16 := by
  simp [instantonRatio, Nc, dimSpinor16, totalStates_eq_sixteen]
  norm_num

/-! ## Equivalent reformulation: `y_c/y_τ = ν / dim(16)` (without N_c) -/

/-- An alternative reading: drop `N_c` from numerator and use the **total**
    instanton number `ν_total = N_c · ν_per_gen · N_gen / N_c = N_gen · ν_per_gen`.

    For `ν_per_gen = 1` and `N_gen = 3`: `ν_total = 3`. -/
def perSpinorRatio (ν_total : ℕ) : ℚ := (ν_total : ℚ) / (dimSpinor16 : ℚ)

@[simp] theorem perSpinorRatio_three :
    perSpinorRatio 3 = 3 / 16 := by
  simp [perSpinorRatio, dimSpinor16, totalStates_eq_sixteen]

/-! ## The two interpretations of "3" in 3/16 -/

/-- **Tier 1.**  The two ways of getting `3/16`:

    (a) `N_c / dim(16)` where `N_c = 3` is the number of colors.
    (b) `ν_total / dim(16)` where `ν_total = 3` is total instanton charge
        (= number of generations × 1 instanton each).

    They give the same number because `N_c = N_gen = 3` in the SM.
    The framework conjectures interpretation (b) is the **topologically
    natural** one. -/
theorem two_interpretations_of_three_over_sixteen :
    charmTauRatio = perSpinorRatio 3 := by
  rw [charmTauRatio_eq, perSpinorRatio_three]

/-! ## Decomposition: per-rep zero-mode counts -/

/-- Atiyah-Singer index in SU(3) representation `R` for instanton charge `ν`.

    Formula (Atiyah-Singer 1968, normalized by `T_2(fund) = 1/2`):

      `index(D_+ in R) = -ν · T_2(R) / T_2(fund) = -ν · doubleDynkin(R)`.

    Sign convention: `index(3) = -ν`, `index(3̄) = +ν` (after charge conjugation).

    We carry the absolute value as a natural number; the sign is encoded
    by the rep type (3 vs 3̄). -/
def absIndex (R : SU3Rep) (ν : ℕ) : ℕ := R.doubleDynkin * ν

/-- Zero modes of negative chirality per copy of SU(3) rep R. -/
def hMinusPerCopy (R : SU3Rep) (ν : ℕ) : ℕ :=
  match R with
  | .three    => absIndex R ν
  | _         => 0

/-- Zero modes of positive chirality per copy of SU(3) rep R. -/
def hPlusPerCopy (R : SU3Rep) (ν : ℕ) : ℕ :=
  match R with
  | .threeBar => absIndex R ν
  | _         => 0

/-- Total negative-chirality zero modes in the 16-spinor for instanton ν. -/
def hMinusIn16 (ν : ℕ) : ℕ :=
  (decomposition.map (fun s =>
    s.count * s.su2.dim * hMinusPerCopy s.su3 ν)).sum

/-- Total positive-chirality zero modes in the 16-spinor for instanton ν. -/
def hPlusIn16 (ν : ℕ) : ℕ :=
  (decomposition.map (fun s =>
    s.count * s.su2.dim * hPlusPerCopy s.su3 ν)).sum

/-- **Tier 1.**  For `ν = 1`, the 16-spinor has 2 zero modes of each chirality. -/
@[simp] theorem hMinus_in_16_one : hMinusIn16 1 = 2 := by decide

@[simp] theorem hPlus_in_16_one : hPlusIn16 1 = 2 := by decide

/-- **Tier 1.**  Anomaly-free: per-generation `h_+ = h_-` (= 2 for ν = 1). -/
theorem anomaly_cancels_in_16_one :
    hPlusIn16 1 = hMinusIn16 1 := by decide

/-- **Tier 1.**  Total zero modes per generation per ν = 1: `h_+ + h_- = 4`. -/
@[simp] theorem total_zero_modes_one : hPlusIn16 1 + hMinusIn16 1 = 4 := by decide

/-! ## The instanton-counting hypothesis -/

/-- **Tier 3.**  The framework's instanton-counting hypothesis.

    The SM gauge bundle on the spectral-triple manifold side carries
    `ν_total` units of SU(3)_c topological charge, with `ν_total =
    N_generations = 3`. The Yukawa-ratio selection `y_c / y_τ` is then
    the per-spinor-state instanton density:

       `y_c / y_τ = ν_total / dim(16) = 3 / 16`.

    This is open: it is the bridge between gauge topology and Yukawa
    selection that the manuscript leaves to a future "rigorous derivation". -/
class InstantonHypothesis (y_c y_τ : ℚ) (ν_total : ℕ) : Prop where
  yτ_pos      : y_τ ≠ 0
  ratio_eq    : y_c / y_τ = perSpinorRatio ν_total
  ν_eq_3      : ν_total = 3   -- = N_generations in SM

/-- Under the instanton-counting hypothesis, `CharmTauHypothesis` follows. -/
instance instantonHypothesis_implies_charmTau
    (y_c y_τ : ℚ) [h : InstantonHypothesis y_c y_τ 3] :
    CharmTauHypothesis y_c y_τ where
  yτ_pos := h.yτ_pos
  ratio  := by
    rw [h.ratio_eq, perSpinorRatio_three]
    simp [Nc, dimSpinor16, totalStates_eq_sixteen]

end SpectralPhysics.YukawaHierarchy
