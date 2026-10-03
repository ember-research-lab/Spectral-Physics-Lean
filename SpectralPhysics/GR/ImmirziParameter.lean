/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Triad.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Field.Basic

/-!
# The Immirzi Parameter (Ch 29) — external input, not derived

**Status (2026-10-03): `gamma` is a `def` set to the literature value
ln(2) / (pi * sqrt(3)) of Ashtekar–Baez–Corichi–Krasnov (1998). Nothing in
this file, or elsewhere in this repo, derives it from the spectral structure.**
The manuscript's `thm:immirzi` was retagged on 2026-09-22 as a back-solve, not a
prediction; this header matches that retag. The parameter controls the quantum
of area in loop quantum gravity: A = 8 pi gamma l_P^2 sqrt(j(j+1)).

## What is actually proved here

* `immirzi_pos` : 0 < gamma  (arithmetic)
* `immirzi_su2_origin` : sqrt(3) = 2 sqrt(j(j+1)) at j = 1/2  (arithmetic identity
  behind the ABCK denominator; no self-reference content)

## Not formalized (honest negative)

The Bekenstein–Hawking matching argument (S_BH = A/(4 l_P^2); LQG area spectrum;
SU(2) puncture counting S = (gamma_0/gamma) A/(4 l_P^2); gamma = gamma_0) is LQG
background and is NOT formalized. A former theorem `immirzi_from_black_hole` stated
this matching but proved only `True`; it was removed on 2026-10-03 as a vacuous
shell (no dependents). Any claim that gamma "arises from the triad spectrum" has
no theorem behind it.

## References

* Ashtekar, Baez, Corichi, Krasnov (1998), gr-qc/9710007 — the value used here
* Immirzi, "Quantum gravity and Regge calculus" (1997)
* Ben-Shalom, "Spectral Physics", Chapter 29 (`thm:immirzi`, retagged 2026-09-22)
-/

noncomputable section

open Real

namespace SpectralPhysics.ImmirziParameter

/-- The Barbero-Immirzi parameter -/
def gamma : ℝ := Real.log 2 / (Real.pi * Real.sqrt 3)

/-- **Immirzi parameter numerical value**: gamma ~ 0.1274.
(The value ln(2)/(π√3) ≈ 0.12738 is the Ashtekar–Baez–Corichi–Krasnov (1998,
gr-qc/9710007) black hole entropy counting with SU(2) Chern-Simons punctures,
j_min = 1/2. Alternatives in the literature: Dreyer (2003, gr-qc/0211076)
ln(3)/(2π√2) ≈ 0.1236 (j_min = 1, SO(3), quasinormal modes);
Domagała–Lewandowski / Meissner (2004, gr-qc/0407051, gr-qc/0407052)
≈ 0.2375 from corrected state counting.) -/
theorem immirzi_pos : 0 < gamma := by
  unfold gamma
  apply div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  exact mul_pos Real.pi_pos (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 3))

/-- **Arithmetic identity behind the ABCK denominator**:
    sqrt(3) = 2 sqrt(j(j+1)) at j = 1/2, the lowest SU(2) representation.
    This is arithmetic only; it relates nothing to self-reference or to the
    golden-ratio structure. -/
theorem immirzi_su2_origin :
    Real.sqrt 3 = 2 * Real.sqrt ((1/2 : ℝ) * (1/2 + 1)) := by
  -- 1/2 * (1/2 + 1) = 3/4, and 2 * sqrt(3/4) = sqrt(4 * 3/4) = sqrt(3)
  have h1 : (1/2 : ℝ) * (1/2 + 1) = 3/4 := by norm_num
  rw [h1]
  rw [show (2 : ℝ) = Real.sqrt 4 from by
    rw [show (4 : ℝ) = 2^2 from by norm_num]; exact (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)).symm]
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

end SpectralPhysics.ImmirziParameter

end
