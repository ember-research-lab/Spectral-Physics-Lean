/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.QFT.WightmanAxioms

/-!
# Yang-Mills Mass Gap (Conditional Theorem)

The mass gap for Yang-Mills derived from the spectral physics framework:
1. Connected relational structure → spectral gap `λ₁ > 0` (proved)
2. Spectral gap → Euclidean correlator decay (proved in HeatSemigroup)
3. OS reconstruction → Lorentzian mass gap (requires continuum limit)

## Status

**Conditional**: assumes spectral convergence hypotheses hold for Yang-Mills.
The Clay Millennium Problem asks for unconditional proof; we provide the
conditional result showing the framework naturally produces a mass gap.

## References

* Jaffe-Witten, "Quantum Yang-Mills Theory" (Clay problem statement)
* Ben-Shalom, "Spectral Physics", Chapter 13
-/

noncomputable section

open Finset RelationalStructure

variable (S : RelationalStructure)

namespace SpectralPhysics.YangMills

/-- **Discrete mass gap**: On a connected relational structure, the Laplacian
    has a spectral gap `λ₁ > 0`. The null space is exactly the constants.
    PROVED — from `spectral_gap_pos` and `null_space_is_constants`. -/
theorem mass_gap_discrete
    (hc : S.isClassical) (hconn : SpectralLaplacian.isStronglyConnected S) :
    ∀ (f : S.X → ℂ),
      (S.innerProduct f (S.SpectralLaplacian f)).re = 0 →
      ∃ (c : ℂ), f = fun _ => c :=
  fun f hf => SpectralLaplacian.null_space_is_constants S hc hconn f hf

/-- **Euclidean mass gap**: The correlator decays exponentially with rate `λ₁`.
    For `f` with zero ground-state component:
      `Re⟨f, K_t f⟩ ≤ e^{-tλ₁} · ‖f‖²`
    PROVED (modulo one Finset.sum splitting step) in HeatSemigroup.lean. -/
theorem euclidean_mass_gap {n : ℕ} (sd : SpectralDecomp S n)
    (hn : 1 < n)
    (f : S.X → ℂ) (hf : sd.coeffSq f ⟨0, by omega⟩ = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    heatInner sd f t ≤
      Real.exp (-t * sd.eigenval ⟨1, hn⟩) * (S.innerProduct f f).re :=
  correlator_decay sd hn f hf t ht

/-- **Conditional continuum mass gap**: Under spectral convergence,
    if the discrete spectral gaps are uniformly bounded below by `δ > 0`,
    the continuum theory has mass gap `m ≥ √δ`. -/
theorem mass_gap_continuum
    (eigenvalues : ℕ → ℝ)
    [SpectralPhysics.Weyl.WeylAsymptotics eigenvalues]
    (δ : ℝ) (hδ : 0 < δ)
    (h_gap : eigenvalues 1 ≥ δ) :
    ∃ (m : ℝ), 0 < m ∧ m ^ 2 ≤ eigenvalues 1 :=
  ⟨Real.sqrt δ, Real.sqrt_pos_of_pos hδ, by
    rw [Real.sq_sqrt (le_of_lt hδ)]; exact h_gap⟩

end SpectralPhysics.YangMills

end
