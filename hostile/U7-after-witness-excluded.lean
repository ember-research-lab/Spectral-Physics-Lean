import SpectralPhysics.MajoranaBlock.SpectralMultiplicity
import SpectralPhysics.MajoranaBlock.HypothesisB
import SpectralPhysics.MajoranaBlock.Discriminator
open SpectralPhysics.MajoranaBlock

/-- The U7 hostile record: KO-dim 6, signs (1,1,−1), ZERO generations.
This is a valid `FiniteSpectralTriple`; it must NOT force `0 = 3`. -/
def hostile : FiniteSpectralTriple :=
  { kodim := 6, j_eps := 1, j_eps_prime := 1, j_eps_double_prime := -1,
    n_generations := 0, extendedDirac := true }

theorem hostile_ko6 : hostile.KOdim_eq_six := rfl
theorem hostile_signs : hostile.J_sign_triple_KO6 := ⟨rfl, rfl, rfl⟩
theorem hostile_zero_generations : hostile.n_generations = 0 := rfl

/-- The 3-generation claim is pinned to `standardModelTriple`, not ∀. -/
theorem sm_three : standardModelTriple.n_generations = 3 :=
  standardModel_three_generations

#print axioms standardModel_three_generations
#print axioms SpectralPhysics.MajoranaBlock.HypothesisB.standardModelTriple_n_generations_eq
#print axioms SpectralPhysics.MajoranaBlock.HypothesisB.standardModelTriple_JSC_multiplicity_eq_six
#print axioms SpectralPhysics.MajoranaBlock.Discriminator.standardModelTriple_JSC_multiplicity_is_six
#print axioms SpectralPhysics.MajoranaBlock.Discriminator.framework_predicts_hypothesisB_with_multiplicity_six
#print axioms SpectralPhysics.MajoranaBlock.Discriminator.standardModelTriple_verdict
