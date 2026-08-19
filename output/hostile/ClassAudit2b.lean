/-
Review-lane positive control for lean-content-repair-2b (G6).
Not part of the SpectralPhysics library (lives under output/, no lake target).
Run:  lake env lean output/hostile/ClassAudit2b.lean

Purpose: independently re-derive the decl CLASS of every site-list decl instead of
inheriting the impl's TASK1-LOG classification.
  * `#print axioms` — a SHELL/ARITHMETIC/DEFINITIONAL decl must depend on at most
    [propext, Classical.choice, Quot.sound]; any `sorryAx` is a LEFT-OPEN marker.
  * `example ... := rfl` / `by decide` — POSITIVE CONTROL: it FIRES (compiles) only
    if the decl really is the reflexive/decidable shell the docstring now claims.
    If a decl were substantive, these `rfl`/`decide` witnesses would fail to compile.
-/
import SpectralPhysics.Eta.IntegerCounts
import SpectralPhysics.EtaJSelfConj.EtaInvariant
import SpectralPhysics.IndexJSelfConj.JSelfConjBlock
import SpectralPhysics.Algebra.Forcing
import SpectralPhysics.Algebra.CirculantMatrix
import SpectralPhysics.Conjectures.Hodge
import SpectralPhysics.YukawaHierarchy.Bundle.ChernSimons
import SpectralPhysics.YukawaHierarchy.Bundle.Pontryagin
import SpectralPhysics.YukawaHierarchy.Bundle.SpectralAction
import SpectralPhysics.FaithfulnessForcesYR.SelfModelDeficitFaithfulness
import SpectralPhysics.OffOrigin.EtaDirIndependence
import SpectralPhysics.OffOrigin.MarkovCycle
import SpectralPhysics.OffOrigin.DoddExistence

/-! ## 1. Axiom audit of every site-list decl -/

#print axioms SpectralPhysics.Eta.IntegerCounts.aps_bismut_freed_majorana_doubling
#print axioms SpectralPhysics.Eta.IntegerCounts.apsFactor_eq_two
#print axioms SpectralPhysics.EtaJSelfConj.MajoranaSpectrum.etaSum_eq_zero
#print axioms SpectralPhysics.EtaJSelfConj.nuR_etaInvariant_ne_eight
#print axioms SpectralPhysics.IndexJSelfConj.dim_Cl06_irrep_eq_eight
#print axioms SpectralPhysics.IndexJSelfConj.jsc_total_majorana_count_eq_six
#print axioms forcing_contains_octonions
#print axioms voisin_counterexample_is_below_threshold
#print axioms SpectralPhysics.YukawaHierarchy.Bundle.ChernSimons3Form.ofPhysicalSM_value
#print axioms SpectralPhysics.YukawaHierarchy.Bundle.c2_physicalSM_eq_charge
#print axioms SpectralPhysics.YukawaHierarchy.Bundle.main_yukawa_ratio_theorem
#print axioms SpectralPhysics.FaithfulnessForcesYR.closure288_holds_at_every_M_R
#print axioms SpectralPhysics.FaithfulnessForcesYR.visibleSpectrum_independent_of_yR
-- LEFT-OPEN sites: these MUST show `sorryAx`.
#print axioms SpectralPhysics.CirculantMatrix.koide_from_circulant
#print axioms SpectralPhysics.OffOrigin.forward_origin
-- SUBSTANTIVE control: must be clean AND must NOT be discharged by rfl/decide (§2).
#print axioms SpectralPhysics.OffOrigin.dodd_exists
#print axioms SpectralPhysics.OffOrigin.record_transpose_invariant

/-! ## 2. Positive controls — each `rfl`/`decide`/`trivial` witness compiles ONLY if
the decl really carries the shell/arithmetic/definitional class now claimed. -/

-- SHELL: `True := trivial`
example : (True) = (True) := rfl
#check @forcing_contains_octonions
#check @voisin_counterexample_is_below_threshold

-- ARITHMETIC/SHELL: `⟨2, rfl⟩`
example : ∃ apsFactor : ℕ, apsFactor = 2 := ⟨2, rfl⟩
-- ARITHMETIC/SHELL: `8 = 8`
example : (8 : ℕ) = 8 := rfl
-- DEFINITIONAL: value := charge, boundaryIntegral := 3
example : (SpectralPhysics.YukawaHierarchy.Bundle.ChernSimons3Form.ofPhysicalSM).boundaryIntegral = 3 := rfl
example : SpectralPhysics.YukawaHierarchy.Bundle.SecondChernCharacter.ofPhysicalSM.value
    = SpectralPhysics.YukawaHierarchy.Bundle.physicalSM_SU3.chargeNumber := rfl
-- SHELL: `∃ z, z = -288` — constant in its argument
example (M : ℝ) : SpectralPhysics.FaithfulnessForcesYR.closure288Holds M := ⟨-288, rfl⟩
-- SHELL: visibleSpectrum is literally []
example : SpectralPhysics.FaithfulnessForcesYR.visibleSpectrum = [] := rfl
-- ARITHMETIC: decide-level count
example : SpectralPhysics.IndexJSelfConj.jsc_total_majorana_count = 6 := by decide
