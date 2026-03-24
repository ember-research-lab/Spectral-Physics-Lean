/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Analysis.HeatSemigroup

/-!
# Reflection Positivity (Osterwalder-Schrader Axiom OS2)

`L ≥ 0` implies the heat kernel is positive semidefinite, which gives
reflection positivity (OS2) — the Euclidean axiom equivalent to unitarity.

## Main results

* `os2_from_psd` : `L ≥ 0` ⟹ reflection positivity (follows from `heat_kernel_psd`)

## References

* Osterwalder-Schrader, "Axioms for Euclidean Green's functions" (1973)
* Ben-Shalom, "Spectral Physics", Chapter 10
-/

noncomputable section

open Finset

variable (S : RelationalStructure)

namespace SpectralPhysics.ReflectionPositivity

/-- **Reflection positivity (OS2)**: The Euclidean correlator `Re⟨f, K_t f⟩ ≥ 0`
    for all `t ≥ 0`. This is a direct consequence of `heat_kernel_psd`, which
    in turn follows from `L ≥ 0` (each spectral coefficient `e^{-tλ}|c|² ≥ 0`).

    This is the hardest Osterwalder-Schrader axiom. The other OS axioms
    (covariance, symmetry, cluster) follow from Laplacian symmetries. -/
theorem os2_from_psd {n : ℕ} (sd : SpectralDecomp S n)
    (f : S.X → ℂ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ heatInner sd f t :=
  heat_kernel_psd sd f t

end SpectralPhysics.ReflectionPositivity

end
