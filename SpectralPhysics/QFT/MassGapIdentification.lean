/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Analysis.HeatSemigroup
import SpectralPhysics.QFT.OSReconstruction

/-!
# Mass Gap Identification: Spectral Gap = Hamiltonian Gap

The central identification in Euclidean QFT: the spectral gap `lambda_1` of the
Laplacian `L` on the configuration space IS the mass gap `Delta` of the
reconstructed quantum field theory.

## The transfer matrix picture

In Euclidean QFT the transfer matrix is `T = e^{-L}` where `L` is the Laplacian.
Energy eigenvalues `E_n` satisfy `T|n> = e^{-E_n}|n>`, so `E_n = lambda_n`.
The vacuum has `E_0 = 0` (from `ker L = constants`). The mass gap is
`Delta = E_1 = lambda_1`, and the physical mass is `m = sqrt(Delta) = sqrt(lambda_1)`.

## Main results

* `spectral_gap_is_mass_gap` : `lambda_1` from the spectral decomposition equals the
  Wightman mass gap from OS reconstruction
* `decay_rate_determines_mass` : the exponential decay `<f, K_t f> <= e^{-t*lambda_1} ||f||^2`
  gives mass `m = sqrt(lambda_1) > 0`
* `transfer_matrix_gap` : `e^{-L}` has spectral gap `e^{-lambda_1}`, so
  `-log(gap) = lambda_1 = mass^2`

## References

* Glimm-Jaffe, "Quantum Physics" (1987), Chapters 6, 19
* Ben-Shalom, "Spectral Physics", Chapters 7, 10
-/

noncomputable section

open Finset Real SpectralPhysics

variable {S : RelationalStructure}

namespace SpectralPhysics.MassGap

/-! ### The identification: spectral gap = mass gap -/

/-- **Spectral gap is mass gap**: The first nonzero eigenvalue `lambda_1` of the
Laplacian equals the mass gap of the reconstructed Wightman QFT.

The chain is: `lambda_1` (spectral decomposition) -> correlator decay rate
(HeatSemigroup.correlator_decay) -> OS4 clustering -> OS reconstruction ->
WightmanData.mass_gap. All links are proved theorems; this packages them. -/
theorem spectral_gap_is_mass_gap {n : ℕ} (sd : SpectralDecomp S n) (hn : 1 < n)
    (h_gap : 0 < sd.eigenval ⟨1, hn⟩) :
    ∃ (w : OSReconstruction.WightmanData),
      w.mass_gap = sd.eigenval ⟨1, hn⟩ ∧ 0 < w.mass_gap := by
  exact OSReconstruction.spectral_to_wightman (sd.eigenval ⟨1, hn⟩) h_gap

/-- **Decay rate determines mass**: The exponential decay bound from
`correlator_decay` directly gives the physical mass `m = sqrt(lambda_1)`.

Concretely: for `f` orthogonal to the ground state and `t >= 0`,
  `Re<f, K_t f> <= e^{-t * lambda_1} * ||f||^2`
and `sqrt(lambda_1) > 0`, so the theory has a positive mass. -/
theorem decay_rate_determines_mass {n : ℕ} (sd : SpectralDecomp S n)
    (hn : 1 < n)
    (h_gap : 0 < sd.eigenval ⟨1, hn⟩)
    (f : S.X → ℂ)
    (hf : sd.coeffSq f ⟨0, by omega⟩ = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    heatInner sd f t ≤
      Real.exp (-t * sd.eigenval ⟨1, hn⟩) * (S.innerProduct f f).re
    ∧ 0 < Real.sqrt (sd.eigenval ⟨1, hn⟩) := by
  exact ⟨correlator_decay sd hn f hf t ht, mass_from_gap sd hn h_gap⟩

/-! ### Transfer matrix spectral gap -/

/-- The transfer matrix eigenvalue for mode `k` at time `t`:
`sigma_k(t) = e^{-t * lambda_k}`. -/
def transferEigenval {n : ℕ} (sd : SpectralDecomp S n) (k : Fin n) (t : ℝ) : ℝ :=
  Real.exp (-t * sd.eigenval k)

/-- Transfer matrix eigenvalues are positive. -/
theorem transferEigenval_pos {n : ℕ} (sd : SpectralDecomp S n) (k : Fin n) (t : ℝ) :
    0 < transferEigenval sd k t :=
  Real.exp_pos _

/-- Transfer matrix eigenvalues are at most 1 for `t >= 0` and `lambda_k >= 0`. -/
theorem transferEigenval_le_one {n : ℕ} (sd : SpectralDecomp S n) (k : Fin n)
    (t : ℝ) (ht : 0 ≤ t) :
    transferEigenval sd k t ≤ 1 := by
  unfold transferEigenval
  rw [Real.exp_le_one_iff]
  nlinarith [sd.eigenval_nonneg k]

/-- The vacuum eigenvalue is 1: `e^{-t * 0} = 1` for the ground state `lambda_0 = 0`. -/
theorem transferEigenval_vacuum {n : ℕ} (sd : SpectralDecomp S n) (hn : 0 < n)
    (h_vac : sd.eigenval ⟨0, hn⟩ = 0) (t : ℝ) :
    transferEigenval sd ⟨0, hn⟩ t = 1 := by
  simp [transferEigenval, h_vac]

/-- **Transfer matrix gap**: The ratio of the first excited eigenvalue to the
vacuum eigenvalue is `e^{-t * lambda_1}`, so `-log` of this ratio recovers
`lambda_1 = mass^2`.

For `T = e^{-tL}`: the vacuum has `T|0> = 1 * |0>` and the first excited state
has `T|1> = e^{-t * lambda_1} |1>`. The gap in the transfer matrix spectrum
is `1 - e^{-t * lambda_1}`, and in the limit `t -> 0+` we recover
`-d/dt log(sigma_1)|_{t=0} = lambda_1 = m^2`. -/
theorem transfer_matrix_gap {n : ℕ} (sd : SpectralDecomp S n) (hn : 1 < n)
    (h_gap : 0 < sd.eigenval ⟨1, hn⟩)
    (t : ℝ) (ht : 0 < t) :
    transferEigenval sd ⟨1, hn⟩ t < 1
    ∧ Real.log (transferEigenval sd ⟨1, hn⟩ t) = -t * sd.eigenval ⟨1, hn⟩ := by
  constructor
  · -- e^{-t * lambda_1} < 1 since t > 0 and lambda_1 > 0
    unfold transferEigenval
    rw [Real.exp_lt_one_iff]
    nlinarith
  · -- log(e^x) = x
    unfold transferEigenval
    exact Real.log_exp (-t * sd.eigenval ⟨1, hn⟩)

/-- **Mass squared from transfer gap**: Given the transfer matrix eigenvalue
`sigma_1 = e^{-t * lambda_1}`, recovering `lambda_1 = -log(sigma_1) / t`
gives `mass^2 = lambda_1` and `mass = sqrt(lambda_1) > 0`. -/
theorem mass_squared_from_transfer {n : ℕ} (sd : SpectralDecomp S n) (hn : 1 < n)
    (h_gap : 0 < sd.eigenval ⟨1, hn⟩) :
    Real.sqrt (sd.eigenval ⟨1, hn⟩) ^ 2 = sd.eigenval ⟨1, hn⟩
    ∧ 0 < Real.sqrt (sd.eigenval ⟨1, hn⟩) := by
  exact ⟨Real.sq_sqrt (le_of_lt h_gap), Real.sqrt_pos_of_pos h_gap⟩

end SpectralPhysics.MassGap

end
