import SpectralPhysics.BasinConnectivity.Verdict

open SpectralPhysics.KSRCompactness SpectralPhysics.BasinConnectivity

noncomputable section

instance : DiscreteTopology KSR := ⟨rfl⟩

/-- In the placeholder (discrete) topology, `BasinConnectivity F` is FALSE for every F. -/
theorem basinConnectivity_false (F : KSR → ℝ) : ¬ BasinConnectivity F := by
  intro h
  have hne : (sublevel F (F KSR.zero - 1)).Nonempty := (h _).nonempty
  obtain ⟨T1, hT1⟩ := hne
  have hlt : F T1 < F KSR.zero := by
    have := (mem_sublevel).mp hT1; linarith
  have hsub : (sublevel F (F KSR.zero)).Subsingleton :=
    IsPreconnected.subsingleton (h (F KSR.zero)).isConnected.isPreconnected
  have h1 : T1 ∈ sublevel F (F KSR.zero) := (mem_sublevel).mpr (le_of_lt hlt)
  have h0 : KSR.zero ∈ sublevel F (F KSR.zero) := (mem_sublevel).mpr (le_refl _)
  have := hsub h1 h0
  subst this
  exact lt_irrefl _ hlt

/-- Hence the "conditional closure" hypotheses are refutable for SAGFfunctional. -/
theorem sagf_hyps_false : ¬ SAGFPalaisSmaleHypotheses :=
  fun h => basinConnectivity_false _ (SAGF_basin_closure_from_hypotheses h)

/-- And the Morse "named axiom" is provable outright in the discrete shadow. -/
theorem morse_provable (F : KSR → ℝ) : MorseObstruction F := by
  intro c ⟨T1, T2, hne, ⟨_, h1⟩, ⟨_, h2⟩⟩
  refine ⟨1, one_pos, fun hpc => ?_⟩
  have hsub := IsPreconnected.subsingleton hpc.isConnected.isPreconnected
  have m1 : T1 ∈ sublevel F (c + 1) := (mem_sublevel).mpr (by linarith)
  have m2 : T2 ∈ sublevel F (c + 1) := (mem_sublevel).mpr (by linarith)
  exact hne (hsub m1 m2)

#print axioms basinConnectivity_false
#print axioms sagf_hyps_false
#print axioms morse_provable
