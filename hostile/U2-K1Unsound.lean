import SpectralPhysics.CompositionUniqueness.KasparovProductUniqueness
open SpectralPhysics.CompositionUniqueness
def zeroOp : BinaryOpOnSpectra := ⟨fun _ _ => (0 : Spectrum)⟩
theorem zeroOp_witness : KasparovProductWitness zeroOp := ⟨fun _ _ => rfl, trivial⟩
theorem false_from_K1 : False := by
  have h := K1_mesland_rennie_card zeroOp_witness ({0} : Multiset ℝ) ({0} : Multiset ℝ)
  simp [zeroOp] at h
theorem false_from_K2 : False := by
  have h := K2_rosenberg_schochet_cancel zeroOp_witness ({0} : Multiset ℝ) ({1} : Multiset ℝ) ({0} : Multiset ℝ)
    (by simp [Spectrum.NonTrivial]) rfl
  have : (0:ℝ) ∈ ({1} : Multiset ℝ) := by rw [← h]; simp
  simp at this
theorem false_from_K3 : False := by
  have h := K3_kassel_residue zeroOp_witness ({1} : Multiset ℝ) ({1} : Multiset ℝ)
  simp [zeroOp, Spectrum.trace] at h
  norm_num at h
#print axioms false_from_K1
#print axioms false_from_K2
#print axioms false_from_K3
