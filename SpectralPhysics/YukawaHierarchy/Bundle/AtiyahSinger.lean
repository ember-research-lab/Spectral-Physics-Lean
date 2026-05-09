/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.YukawaHierarchy.Bundle.InstantonNumber
import SpectralPhysics.YukawaHierarchy.Bundle.ChernSimons
import SpectralPhysics.YukawaHierarchy.InstantonCounting

/-!
# Atiyah-Singer Index Theorem — Extended Scaffolding

For a connection on a principal SU(N) bundle of charge `ν` over `S⁴`, the
twisted Dirac operator `D_R` in representation `R` has

  `index(D_R^+) = -ν · T_2(R) / T_2(fund) = -2 ν T_2(R)`        (in our normalisation)

where `T_2(fund SU(N)) = 1/2`.

We use this to:
* Identify zero-mode counts in each SU(3) sub-rep of the SO(10) 16-spinor.
* Sum these into the per-generation total `h_+ = h_- = 2 ν` (anomaly-free).
* Bridge to the `InstantonHypothesis` from `InstantonCounting.lean`.

## Tier classification

* **Tier 3 (hypothesised)**: the Atiyah-Singer index theorem itself
  (we instantiate it as a typeclass `AtiyahSingerIndex` extending the
  one in `PrincipalBundle.lean`).
* **Tier 1 (proved)**: all consequences once the AS hypothesis is
  granted — Dynkin scaling, index sum over the 16-decomposition,
  anomaly cancellation, bridge to `InstantonHypothesis`.

## References

* Atiyah, M.F., Singer, I.M. (1968). "The index of elliptic operators I–IV."
* Atiyah, M.F., Hitchin, N.J., Singer, I.M. (1978). "Self-duality in
  4-d Riemannian geometry."
-/

namespace SpectralPhysics.YukawaHierarchy.Bundle

open SpectralPhysics.YukawaHierarchy

/-! ## Index sum over the SO(10) 16-spinor decomposition -/

/-- The Atiyah-Singer index of `D_+` summed over the SO(10) 16-spinor's
    decomposition into SU(3) sub-reps, for a bundle of charge `ν`.

    Concretely:
      Σ over (R_color, R_iso, count) ∈ 16-decomp of
        count · dim(R_iso) · signedIndex(R_color) · ν
      = 2 · (-1) · ν + 2 · (+1) · ν + 0  =  0   (anomaly-free).

    The factor `dim(R_iso)` accounts for the SU(2) doublet multiplicity. -/
def signedDoubleDynkin (R : SU3Rep) : ℤ :=
  match R with
  | SU3Rep.three    => -(R.doubleDynkin : ℤ)
  | SU3Rep.threeBar => (R.doubleDynkin : ℤ)
  | SU3Rep.one      => 0

def indexSum_in_16 (ν : ℤ) : ℤ :=
  (decomposition.map (fun s =>
    (s.count : ℤ) * (s.su2.dim : ℤ) * signedDoubleDynkin s.su3 * ν)).sum

/-- Closed-form value: the per-`ν` coefficient. -/
def indexSum_coeff : ℤ :=
  (decomposition.map (fun s =>
    (s.count : ℤ) * (s.su2.dim : ℤ) * signedDoubleDynkin s.su3)).sum

/-- The coefficient is 0 (anomaly-free SM). -/
theorem indexSum_coeff_eq_zero : indexSum_coeff = 0 := by decide

/-- `indexSum_in_16 ν = indexSum_coeff · ν = 0`.

    Direct expansion: `decomposition` has 6 explicit elements, so the
    list sum unfolds to a sum of 6 products that we can factor by `ring`. -/
theorem indexSum_in_16_factored (ν : ℤ) :
    indexSum_in_16 ν = indexSum_coeff * ν := by
  show ((decomposition.map (fun s =>
    (s.count : ℤ) * (s.su2.dim : ℤ) * signedDoubleDynkin s.su3 * ν)).sum)
    = (decomposition.map (fun s =>
    (s.count : ℤ) * (s.su2.dim : ℤ) * signedDoubleDynkin s.su3)).sum * ν
  -- Unfold the explicit 6-element list
  show ((decomposition.map _).sum) = ((decomposition.map _).sum) * ν
  unfold decomposition
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
              signedDoubleDynkin]
  ring

/-- **Tier 1.**  General anomaly cancellation: for any `ν : ℤ`,
    `indexSum_in_16 ν = 0`. -/
theorem indexSum_in_16_zero (ν : ℤ) : indexSum_in_16 ν = 0 := by
  rw [indexSum_in_16_factored, indexSum_coeff_eq_zero, zero_mul]

/-- **Tier 1.**  For one instanton (`ν = 1`) the AS index in 16 is `0`. -/
@[simp] theorem indexSum_in_16_one : indexSum_in_16 1 = 0 :=
  indexSum_in_16_zero 1

/-- **Tier 1.**  For three instantons (`ν = 3`) the AS index in 16 is `0`. -/
@[simp] theorem indexSum_in_16_three : indexSum_in_16 3 = 0 :=
  indexSum_in_16_zero 3

/-! ## Per-chirality zero-mode counts in the 16 -/

/-- Negative-chirality zero-mode count in the 16-spinor for charge `ν ≥ 0`. -/
def hMinus_per_16 (ν : ℕ) : ℕ :=
  (decomposition.map (fun s =>
    s.count * s.su2.dim *
      (match s.su3 with
       | SU3Rep.three    => s.su3.doubleDynkin * ν
       | _               => 0))).sum

/-- Positive-chirality zero-mode count in the 16-spinor for charge `ν ≥ 0`. -/
def hPlus_per_16 (ν : ℕ) : ℕ :=
  (decomposition.map (fun s =>
    s.count * s.su2.dim *
      (match s.su3 with
       | SU3Rep.threeBar => s.su3.doubleDynkin * ν
       | _               => 0))).sum

/-- **Tier 1.**  `h_-(ν=1) = 2` per generation. -/
@[simp] theorem hMinus_per_16_one : hMinus_per_16 1 = 2 := by decide

/-- **Tier 1.**  `h_+(ν=1) = 2` per generation. -/
@[simp] theorem hPlus_per_16_one : hPlus_per_16 1 = 2 := by decide

/-- **Tier 1.**  Per generation, `h_-(ν) = 2ν` and `h_+(ν) = 2ν` linearly. -/
theorem hMinus_per_16_eq (ν : ℕ) : hMinus_per_16 ν = 2 * ν := by
  unfold hMinus_per_16 decomposition
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
              SU2Rep.dim, SU3Rep.doubleDynkin]
  ring

theorem hPlus_per_16_eq (ν : ℕ) : hPlus_per_16 ν = 2 * ν := by
  unfold hPlus_per_16 decomposition
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
              SU2Rep.dim, SU3Rep.doubleDynkin]
  ring

/-- **Tier 1.**  Per generation: `h_+(ν) = h_-(ν)`, the anomaly-free condition. -/
theorem chirality_balance (ν : ℕ) :
    hPlus_per_16 ν = hMinus_per_16 ν := by
  rw [hPlus_per_16_eq, hMinus_per_16_eq]

/-- **Tier 1.**  Per generation total `h(ν) = h_+ + h_- = 4ν`. -/
theorem total_zero_modes_per_16 (ν : ℕ) :
    hPlus_per_16 ν + hMinus_per_16 ν = 4 * ν := by
  rw [hPlus_per_16_eq, hMinus_per_16_eq]
  ring

/-! ## Multi-generation totals -/

/-- For `N_gen` generations and `ν_per_gen` instantons each: total negative-chirality
    zero modes = `N_gen · h_-(ν_per_gen) = N_gen · 2 · ν_per_gen`. -/
def hMinus_total (Ngen : ℕ) (νPerGen : ℕ) : ℕ := Ngen * hMinus_per_16 νPerGen

/-- Same for positive-chirality. -/
def hPlus_total (Ngen : ℕ) (νPerGen : ℕ) : ℕ := Ngen * hPlus_per_16 νPerGen

/-- **Tier 1.**  Total `ν_total = N_gen · ν_per_gen` matches the manifold-side
    bundle charge.

    In the SM, `N_gen = 3`, `ν_per_gen = 1`, so `ν_total = 3` = charge
    of `physicalSM_SU3`. -/
def νTotal (Ngen : ℕ) (νPerGen : ℕ) : ℕ := Ngen * νPerGen

/-- For SM: `νTotal 3 1 = 3 = physicalSM_SU3.chargeNumber`. -/
@[simp] theorem νTotal_SM : (νTotal 3 1 : ℤ) = physicalSM_SU3.chargeNumber := by
  unfold νTotal; decide

/-! ## Bridge to InstantonHypothesis -/

/-- **Tier 1.**  `instantonRatio` from `InstantonCounting.lean`, for the
    framework's `ν = 1` per-generation, equals `N_c / dim(16)`. -/
theorem instantonRatio_νTotal_three :
    perSpinorRatio (νTotal 3 1) = charmTauRatio := by
  -- νTotal 3 1 = 3, perSpinorRatio 3 = 3/16 = charmTauRatio.
  rfl

/-- **Tier 1.**  Putting it together: under `BridgeConjecture`,
    `y_c / y_τ = (νTotal 3 1) / dim(16) = 3 / 16`. -/
theorem ratio_via_bundle_charge_in_real
    (y_c y_τ : ℝ) (hτ : y_τ ≠ 0)
    (h : BridgeConjecture y_c y_τ) :
    y_c / y_τ = (νTotal 3 1 : ℝ) / (dimSpinor16 : ℝ) := by
  have h1 : y_c / y_τ = 3 / (dimSpinor16 : ℝ) :=
    bridgeConjecture_implies_real_ratio y_c y_τ hτ h
  rw [h1]
  show (3 : ℝ) / (dimSpinor16 : ℝ) = (νTotal 3 1 : ℝ) / (dimSpinor16 : ℝ)
  unfold νTotal
  push_cast
  ring

end SpectralPhysics.YukawaHierarchy.Bundle
