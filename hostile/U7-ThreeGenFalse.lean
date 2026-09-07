import SpectralPhysics.MajoranaBlock.SpectralMultiplicity

open SpectralPhysics.MajoranaBlock

/-! Hostile-before for U7 (2026-08-18 content audit).

The deleted `∀`-axiom

  `axiom standardModel_three_generations :
      ∀ T : FiniteSpectralTriple,
        T.KOdim_eq_six → T.J_sign_triple_KO6 → T.n_generations = 3`

quantified over the *free* structure `FiniteSpectralTriple`. The
witness `{kodim := 6, signs (1,1,−1), n_generations := 0}` satisfies
both hypotheses and forces `0 = 3`. This file re-declares that axiom
locally (the library copy is gone) and derives `False`. -/

axiom standardModel_three_generations_forall :
    ∀ T : FiniteSpectralTriple,
      T.KOdim_eq_six → T.J_sign_triple_KO6 → T.n_generations = 3

def hostile : FiniteSpectralTriple :=
  { kodim := 6
    j_eps := 1
    j_eps_prime := 1
    j_eps_double_prime := -1
    n_generations := 0
    extendedDirac := true }

theorem hostile_ko6 : hostile.KOdim_eq_six := rfl

theorem hostile_signs : hostile.J_sign_triple_KO6 := ⟨rfl, rfl, rfl⟩

theorem u7_false : False := by
  have h : hostile.n_generations = 3 :=
    standardModel_three_generations_forall hostile hostile_ko6 hostile_signs
  simp [hostile] at h

#print axioms u7_false
