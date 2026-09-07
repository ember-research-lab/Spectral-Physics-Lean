/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SelfModelDeficitUnconditional.PhysicalSpectrum
import SpectralPhysics.SelfModelDeficitUnconditional.UnconditionalGoal
import SpectralPhysics.SelfModelDeficitUnconditional.Verdict
import SpectralPhysics.SelfModelDeficitRigorous.Theorem
import SpectralPhysics.SelfModelDeficitRigorous.FaithfulState
import Mathlib.Tactic.NormNum

/-!
# Hostile check — SelfModelDeficitUnconditional, 2026-09-06

(a) The single-mode `y = 1` spectrum is a `VisibleSpectrum` (no
    physicality filter).  Its information content is 0, so 288 does
    **not** follow.  Completeness holds (`0 ≤ 288`); sector-faithfulness
    fails (`288 ≤ 0`).  `CapacityPosit288` fails.

(b) `#print axioms` on every rewritten theorem — kernel only
    (`propext`, `Classical.choice`, `Quot.sound`).
-/

open SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta
open SpectralPhysics.SelfModelDeficitRigorous.FaithfulState
open SpectralPhysics.SelfModelDeficitRigorous.Theorem
open SpectralPhysics.SelfModelDeficitUnconditional.PhysicalSpectrum
open SpectralPhysics.SelfModelDeficitUnconditional.UnconditionalGoal
open SpectralPhysics.SelfModelDeficitUnconditional.Verdict

/-- (a) Counterexample spectrum is admissible: it is the named
`counterexampleSpectrum` (`VisibleSpectrum`, no `IsPhysicalSpectrum`
guard). -/
noncomputable example : VisibleSpectrum := counterexampleSpectrum

theorem counterexample_negZeta :
    negZetaPrimeAtZero counterexampleSpectrum = 0 := by
  rw [negZetaPrimeAtZero_eq, counterexampleSpectrum_content]

theorem counterexample_content_ne_288 :
    informationContent counterexampleSpectrum ≠ (288 : ℝ) := by
  rw [counterexampleSpectrum_content]
  norm_num

/-- 288 does not follow: the conclusion is false on this spectrum. -/
theorem counterexample_conclusion_false :
    negZetaPrimeAtZero counterexampleSpectrum ≠ (288 : ℝ) := by
  rw [counterexample_negZeta]
  norm_num

/-- Completeness holds on the counterexample (`0 ≤ 288`). -/
theorem counterexample_completeness :
    CompletenessAtLevel2 spectralPhysicsSectoredAlgebra
      (negZetaPrimeAtZero counterexampleSpectrum) := by
  unfold CompletenessAtLevel2
  rw [counterexample_negZeta, spectralPhysicsSectoredAlgebra_dimHid]
  norm_num

/-- Sector-faithfulness fails (`288 ≤ 0` is false).  The sandwich
cannot fire. -/
theorem counterexample_not_sector_faithful :
    ¬ SectorFaithfulNoDeadWeight spectralPhysicsSectoredAlgebra
        (negZetaPrimeAtZero counterexampleSpectrum) := by
  unfold SectorFaithfulNoDeadWeight
  rw [counterexample_negZeta, spectralPhysicsSectoredAlgebra_dimHid]
  norm_num

/-- Named H4 posit fails on the counterexample. -/
example : ¬ CapacityPosit288 counterexampleSpectrum :=
  counterexampleSpectrum_not_CapacityPosit288

-- (b) axiom audit: rewritten theorems + the sandwich they re-export
#print axioms self_model_deficit_conditional
#print axioms self_model_deficit_conditional_explicit
#print axioms self_model_deficit_conditional_param
#print axioms self_model_deficit_conditional_explicit_param
#print axioms v092_partial_verdict_holds
#print axioms V092PartialVerdict
#print axioms self_model_deficit_theorem_288
#print axioms CapacityPosit288
#print axioms witnessSpectrum_CapacityPosit288
#print axioms counterexampleSpectrum_not_CapacityPosit288
#print axioms counterexample_conclusion_false
#print axioms counterexample_completeness
#print axioms counterexample_not_sector_faithful
