import SpectralPhysics.CompositionUniqueness.KasparovProductUniqueness
open SpectralPhysics.CompositionUniqueness

/-- The U2 zero witness: constant-zero binary operation. -/
def zeroOp : BinaryOpOnSpectra := ⟨fun _ _ => (0 : Spectrum)⟩

/-- Symmetry still holds. -/
theorem zeroOp_symm : ∀ μ ν : Spectrum, zeroOp μ ν = zeroOp ν μ :=
  fun _ _ => rfl

/-- After 2026-09-06, `KasparovProductWitness` requires `card_mul`.
This is the excluded goal: `card 0 = card μ * card ν` is false for
nonempty factors. Expected: this file does **not** compile (unsolved
`card_mul` goal, or a later `False` if someone closes it with sorry). -/
theorem zeroOp_witness : KasparovProductWitness zeroOp :=
  ⟨zeroOp_symm, fun μ ν => by
    -- card (zeroOp μ ν) = card 0 = 0
    -- card μ * card ν is not identically 0
    simp [zeroOp]⟩
