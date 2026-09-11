-- U10 (2026-09-10 soundness census). Derived False from the post-U1-fix
-- `morse_two_minima_disconnect` at 193c3c3. Expected now: does NOT compile
-- (axiom deleted in 9097d36). The in-build pin is
-- `BasinConnectivity.morse_obstruction_not_universal`.
import SpectralPhysics.BasinConnectivity.MorseObstruction
/-! HOSTILE H01 — `morse_two_minima_disconnect` after the U1 fix (2026-09-06).
The ⊥ instance was removed; the axiom now carries an auto-bound
`[TopologicalSpace KSR]` binder, i.e. it is ∀-quantified over ALL topologies.
Instantiate with the indiscrete topology ⊤: two distinct points are both
local minima of F ≡ 0, but every nonempty set is path-connected. -/
open SpectralPhysics.KSRCompactness SpectralPhysics.BasinConnectivity

noncomputable section

#check @morse_two_minima_disconnect

def ksrF : KSR := { lam := fun _ => 0, trace_class := by simp, srInvariant := False }

theorem zero_ne_ksrF : KSR.zero ≠ ksrF := by
  intro h
  have h' : KSR.zero.srInvariant = ksrF.srInvariant := by rw [h]
  have : (True : Prop) = False := h'
  exact (this ▸ trivial : False)

/-- A path in the indiscrete topology between any two points. -/
def topPath (x y : KSR) : @Path KSR ⊤ x y :=
  @Path.mk KSR ⊤ x y
    (@ContinuousMap.mk _ _ _ ⊤ (fun t => if (t : ℝ) = 1 then y else x) continuous_top)
    (by simp) (by simp)

theorem morse_false : False := by
  letI : TopologicalSpace KSR := ⊤
  have hM : MorseObstruction (fun _ : KSR => (0 : ℝ)) := morse_two_minima_disconnect _
  have hTwo : TwoDistinctMinimaAt (fun _ : KSR => (0 : ℝ)) 0 :=
    ⟨KSR.zero, ksrF, zero_ne_ksrF,
      ⟨⟨Set.univ, trivial, isOpen_univ, fun _ _ => le_refl _⟩, rfl⟩,
      ⟨⟨Set.univ, trivial, isOpen_univ, fun _ _ => le_refl _⟩, rfl⟩⟩
  obtain ⟨ε, hε, hnot⟩ := hM 0 hTwo
  apply hnot
  refine ⟨KSR.zero, ?_, fun {y} _ => ⟨topPath KSR.zero y, fun t => ?_⟩⟩
  · show (0 : ℝ) ≤ 0 + ε; linarith
  · show (0 : ℝ) ≤ 0 + ε; linarith

#print axioms morse_false
