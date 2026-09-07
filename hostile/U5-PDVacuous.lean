import SpectralPhysics.DixonPoincareDuality.Verdict

open SpectralPhysics.DixonPoincareDuality SpectralPhysics.DixonOrderOne CayleyDickson

theorem oct_zero_ne_one : (0 : OctonionFactor) ≠ 1 := by
  intro h
  have := congrArg CayleyDickson.fst h
  simp at this

/-- No spectral triple whatsoever satisfies the file's `PoincareDuality` predicate:
a map `𝕆 → (𝕆 → 𝕆)` is never surjective (Cantor). -/
theorem poincareDuality_never (T : AbstractSpectralTriple) : ¬ PoincareDuality T := by
  intro ⟨_, hsurj⟩
  classical
  apply Function.cantor_surjective (fun a : OctonionFactor => {x | T.intersectionForm a x = 1})
  intro s
  obtain ⟨a, ha⟩ := hsurj (fun x => if x ∈ s then (1 : OctonionFactor) else 0)
  refine ⟨a, ?_⟩
  ext x
  have hax : T.intersectionForm a x = (if x ∈ s then (1 : OctonionFactor) else 0) :=
    congrFun ha x
  simp only [Set.mem_setOf_eq]
  rw [hax]
  by_cases hx : x ∈ s <;> simp [hx, oct_zero_ne_one]

theorem connes_PD_definition_vacuous : ∀ T : AbstractSpectralTriple, PDImpliesWellDefined T :=
  fun T h => absurd h (poincareDuality_never T)

theorem dixon_pd_obstruction_shell : ¬ ∃ T : AbstractSpectralTriple, IsCanonicalDixon T ∧ PoincareDuality T :=
  fun ⟨T, _, h⟩ => poincareDuality_never T h

#print axioms poincareDuality_never
#print axioms connes_PD_definition_vacuous
#print axioms dixon_pd_obstruction_shell
