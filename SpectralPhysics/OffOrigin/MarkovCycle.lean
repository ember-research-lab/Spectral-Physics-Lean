/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# The n=3 detailed-balance / cycle-current identity (F3 anchor, toy scale)

Task 3 of the `krein-orientation-lean` spec (companion note:
`krein-orientation-note.tex`, §"The F3 anchor"). For the 3-state Markov generator
with uniform forward rate `k_f` and backward rate `k_b` (uniform stationary
measure, so the π-symmetrization `D_π^{1/2} W D_π^{-1/2}` is trivial at this tier):

* `detailed_balance_iff_symm` — detailed balance (`k_f = k_b`) ⟺ the generator is
  symmetric ⟺ its antisymmetric part vanishes (⟺ `σ_P = 0`,
  `detailed_balance_iff_sigma_zero`).
* `sigma_eq_current_sign` — `σ_P` of the generator (real form:
  `sign tr(Rᵀ A)`, `R = P − Pᵀ`, `A` the antisymmetric part) equals
  `sign(k_f − k_b)`, the direction of the stationary cycle current. Proved
  unconditionally (the spec's `k_f ≠ k_b` hypothesis is not needed: at detailed
  balance both sides are 0).

This is the F3 reduction's core identity at `n = 3`: the felt-arrow formalization
(broken detailed balance, stochastic thermodynamics) lands on the same
frame-relative invariant as the generation-space chamber bit
(`OrientationLemma.sigma_reads_sign`). Sign conventions are LOCKED to the note:
`σ_P(G) = sign tr(Rᵀ A)` for real generators; with these, `σ = sign(k_f − k_b)`.
The general-`n` statement (cycle decomposition; which cycle's frame) is OPEN —
promotion target, specced separately.

NOTE: works over ℝ throughout; deliberately does not import
`EtaDirIndependence.lean` (which carries the OPEN `forward_origin` sorry and is
kept out of the root build) — `antisymmetricPart` here mirrors its
`symmetricPart` convention `(2:ℝ)⁻¹ • (M ± Mᵀ)`.
-/

namespace SpectralPhysics.OffOrigin

open Matrix

section MarkovCycle

/-- The 3-cycle permutation matrix over ℝ (the real form of the frame `P3`;
the cycle orientation on the Markov graph is the frame). -/
def Pr : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0; 0, 0, 1; 1, 0, 0]

/-- The antisymmetric circulant direction `R = P − Pᵀ` — the reference the
frame-relative invariant pairs against. -/
def Rr : Matrix (Fin 3) (Fin 3) ℝ := Pr - Prᵀ

/-- Antisymmetric part of a real square matrix (mirror of `symmetricPart` in
`EtaDirIndependence.lean`). -/
noncomputable def antisymmetricPart (M : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (2 : ℝ)⁻¹ • (M - Mᵀ)

/-- The frame-relative orientation invariant, real form (locked convention):
`σ_P(G) = sign ⟨R, A⟩_F = sign tr(Rᵀ A)` with `A` the antisymmetric part of `G`. -/
noncomputable def sigmaPReal (G : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  Real.sign (Matrix.trace (Rrᵀ * antisymmetricPart G))

/-- The 3-state Markov generator with uniform forward rate `k_f` (along the
cycle `P`) and backward rate `k_b`: `W = k_f•P + k_b•Pᵀ − (k_f+k_b)•1`.
Rows and columns sum to zero; the stationary measure is uniform, so the
π-symmetrized conjugation is trivial. -/
noncomputable def markovGen (kf kb : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  kf • Pr + kb • Prᵀ - (kf + kb) • (1 : Matrix (Fin 3) (Fin 3) ℝ)

/-- Entrywise form of the generator (all downstream computation routes through
this). -/
theorem markovGen_entries (kf kb : ℝ) :
    markovGen kf kb =
      !![-(kf + kb), kf, kb;
         kb, -(kf + kb), kf;
         kf, kb, -(kf + kb)] := by
  ext i j
  simp only [markovGen, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.transpose_apply, Matrix.one_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [Pr]

/-- Entrywise form of the frame direction `R = P − Pᵀ`. -/
theorem Rr_entries :
    Rr = !![0, 1, -1; -1, 0, 1; 1, -1, 0] := by
  ext i j
  simp only [Rr, Matrix.sub_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp [Pr]

/-- Transpose of the generator swaps the rates. -/
theorem markovGen_transpose (kf kb : ℝ) :
    (markovGen kf kb)ᵀ = markovGen kb kf := by
  rw [markovGen_entries, markovGen_entries]
  ext i j
  simp only [Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- Antisymmetric part of the generator: `A = ((k_f − k_b)/2) • (P − Pᵀ)` —
the cycle-current direction times the frame. -/
theorem markovGen_antisymmetricPart (kf kb : ℝ) :
    antisymmetricPart (markovGen kf kb) = ((kf - kb) / 2) • Rr := by
  unfold antisymmetricPart
  rw [markovGen_transpose, markovGen_entries, markovGen_entries, Rr_entries]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- **Task 3.1 — `detailed_balance_iff_symm`.** Detailed balance (`k_f = k_b`)
⟺ the generator is symmetric ⟺ its antisymmetric part is `0`. -/
theorem detailed_balance_iff_symm (kf kb : ℝ) :
    (kf = kb ↔ (markovGen kf kb)ᵀ = markovGen kf kb) ∧
      ((markovGen kf kb)ᵀ = markovGen kf kb ↔
        antisymmetricPart (markovGen kf kb) = 0) := by
  have hentry : ∀ k k' : ℝ, markovGen k k' 0 1 = k := by
    intro k k'
    rw [markovGen_entries]
    simp
  have hsymm_iff : ((markovGen kf kb)ᵀ = markovGen kf kb) ↔ kf = kb := by
    constructor
    · intro h
      have h01 := congrFun (congrFun h 0) 1
      rw [markovGen_transpose, hentry kb kf, hentry kf kb] at h01
      exact h01.symm
    · intro h
      rw [markovGen_transpose, h]
  constructor
  · exact hsymm_iff.symm
  · constructor
    · intro h
      rw [markovGen_antisymmetricPart, show kf - kb = 0 by linarith [hsymm_iff.mp h]]
      simp
    · intro h
      rw [markovGen_antisymmetricPart, Rr_entries] at h
      have h01 := congrFun (congrFun h 0) 1
      simp [Matrix.smul_apply] at h01
      apply hsymm_iff.mpr
      linarith

/-- Frobenius pairing of the frame with itself: `tr(Rᵀ R) = 6`
(the six off-diagonal `±1` entries). -/
theorem trace_Rr_pairing : Matrix.trace (Rrᵀ * Rr) = 6 := by
  rw [Rr_entries]
  simp [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three]
  norm_num

/-- **Task 3.2 — `sigma_eq_current_sign`.** `σ_P` of the 3-state generator equals
the sign of `k_f − k_b` — the direction of the stationary cycle current, the
standard object of stochastic thermodynamics. Proved without the `k_f ≠ k_b`
hypothesis (at detailed balance both sides vanish; cf.
`detailed_balance_iff_sigma_zero`). -/
theorem sigma_eq_current_sign (kf kb : ℝ) :
    sigmaPReal (markovGen kf kb) = Real.sign (kf - kb) := by
  unfold sigmaPReal
  rw [markovGen_antisymmetricPart, Matrix.mul_smul, Matrix.trace_smul,
    trace_Rr_pairing, smul_eq_mul]
  have h3 : (kf - kb) / 2 * 6 = 3 * (kf - kb) := by ring
  rw [h3]
  rcases lt_trichotomy (kf - kb) 0 with h | h | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (by linarith)]
  · rw [h]; norm_num
  · rw [Real.sign_of_pos h, Real.sign_of_pos (by linarith)]

/-- Note's fourth equivalent: detailed balance ⟺ `σ_P = 0` (the bit is
*undefined*, not negative, at the self-adjoint origin). -/
theorem detailed_balance_iff_sigma_zero (kf kb : ℝ) :
    kf = kb ↔ sigmaPReal (markovGen kf kb) = 0 := by
  rw [sigma_eq_current_sign, Real.sign_eq_zero_iff, sub_eq_zero]

end MarkovCycle

/-! ### Axiom audit (compile-time) — recorded in `OffOrigin/STATUS.md`. -/
#print axioms markovGen_transpose
#print axioms markovGen_antisymmetricPart
#print axioms detailed_balance_iff_symm
#print axioms trace_Rr_pairing
#print axioms sigma_eq_current_sign
#print axioms detailed_balance_iff_sigma_zero

end SpectralPhysics.OffOrigin
