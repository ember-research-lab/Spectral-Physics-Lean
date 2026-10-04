import SpectralPhysics.CompositionUniqueness.KasparovProductUniqueness
open SpectralPhysics.CompositionUniqueness

/-- The U2 zero witness: constant-zero binary operation. -/
def zeroOp : BinaryOpOnSpectra := ⟨fun _ _ => (0 : Spectrum)⟩

/-- Symmetry still holds. -/
theorem zeroOp_symm : ∀ μ ν : Spectrum, zeroOp μ ν = zeroOp ν μ :=
  fun _ _ => rfl

/-- After 2026-10-04 (Spectral-Physics-Lean#9 option 2), `KasparovProductWitness`
requires `sq_shape` (spec D² = λ²+μ²). `zeroOp` violates it: squares of
`zeroOp {1} {1}` = {} but additiveConv {1} {1} = {2}.
Expected: this file does **not** compile (unsolved `sq_shape` goal). -/
theorem zeroOp_witness : KasparovProductWitness zeroOp :=
  ⟨zeroOp_symm, fun μ ν => by
    simp [zeroOp]⟩
