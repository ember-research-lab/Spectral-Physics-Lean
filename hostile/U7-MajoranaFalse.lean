import SpectralPhysics.MajoranaBlock.SpectralMultiplicity
open SpectralPhysics SpectralPhysics.MajoranaBlock
-- hostile witness: a "finite spectral triple" with KO-dim 6, signs (1,1,-1), and ZERO generations
def hostile : SpectralPhysics.MajoranaBlock.FiniteSpectralTriple :=
  { kodim := 6, j_eps := 1, j_eps_prime := 1, j_eps_double_prime := -1, n_generations := 0, extendedDirac := true }
theorem hostile_ko6 : hostile.KOdim_eq_six := by unfold FiniteSpectralTriple.KOdim_eq_six hostile; rfl
theorem hostile_signs : hostile.J_sign_triple_KO6 := by
  unfold FiniteSpectralTriple.J_sign_triple_KO6 hostile; exact ⟨rfl, rfl, rfl⟩
theorem false_from_three_generations : False := by
  have h := SpectralPhysics.MajoranaBlock.standardModel_three_generations hostile hostile_ko6 hostile_signs
  simp [hostile] at h
#print axioms false_from_three_generations
