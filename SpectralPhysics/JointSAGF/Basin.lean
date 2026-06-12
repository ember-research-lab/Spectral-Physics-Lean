/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom, Claude (Anthropic)
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Joint-SAGF J5: The quadratic-basin split (√Q amplitude vs. relaxation rate)

Near a nondegenerate critical point, the spectral action is quadratic in the
displacement. Two distinct quantities were previously conflated in the
`C_eff` equation (Third Path v5, Remark 3; April 26 session finding):

* the **amplitude map** (static): functional deficit `Q` determines
  displacement `|x| = √(2Q/h)` — this IS the `√Q` scaling, derived rather
  than ansatz;
* the **relaxation rate** (dynamic): gradient flow in the basin decays
  exponentially at rate `h = λ_min(Hess)`, independent of `Q` — this is
  what the empirical 5–10 turn recovery measures.

The April finding ("√Q implies near-instantaneous recovery, contradicting
the 5–10 turns") assumed one quantity where there are two; both survive.
This file checks the 1-D core of each statement.

## Main results

* `basin_amplitude_sqrt` : for `S(x) = h·x²/2`, deficit `Q := S x` gives
  `|x| = √(2Q/h)`
* `basin_relaxation` : `x(t) = x₀·exp(-h·t)` satisfies the gradient flow
  `x' = -h·x`
* `basin_deficit_decay` : the deficit along the flow decays as `exp(-2h·t)`
-/

namespace SpectralPhysics.JointSAGF

/-- **J5a (amplitude map).** For the quadratic basin `S(x) = h·x²/2` with
`h > 0`, the displacement is the square root of (twice) the deficit over the
curvature: `|x| = √(2·S(x)/h)`. The `√Q` scaling of the `C_eff` equation is
the generic geometry of a nondegenerate basin, not a phenomenological ansatz. -/
theorem basin_amplitude_sqrt (h x : ℝ) (hh : 0 < h) :
    |x| = Real.sqrt (2 * (h * x ^ 2 / 2) / h) := by
  rw [show 2 * (h * x ^ 2 / 2) / h = x ^ 2 by field_simp]
  exact (Real.sqrt_sq_eq_abs x).symm

/-- **J5b (relaxation dynamics).** The trajectory `x(t) = x₀·exp(-h·t)`
satisfies the 1-D gradient flow `x'(t) = -h·x(t)` of the quadratic basin.
The relaxation timescale is `1/h`, set by the curvature (Hessian eigenvalue),
not by the deficit. -/
theorem basin_relaxation (h x₀ : ℝ) (t : ℝ) :
    HasDerivAt (fun s => x₀ * Real.exp (-h * s))
      (-h * (x₀ * Real.exp (-h * t))) t := by
  have h1 : HasDerivAt (fun s : ℝ => -h * s) (-h) t := by
    simpa using (hasDerivAt_id t).const_mul (-h)
  have h2 := (Real.hasDerivAt_exp (-h * t)).comp t h1
  have h3 := h2.const_mul x₀
  convert h3 using 1
  ring

/-- **J5c (deficit decay).** Along the relaxation trajectory the deficit
decays at twice the rate: `S(x(t)) = S(x₀)·exp(-2h·t)`. Recovery *time* is
therefore `O(1/h)` regardless of the `√Q` amplitude relation — the two
claims the April session found in conflict are about different quantities. -/
theorem basin_deficit_decay (h x₀ t : ℝ) :
    h * (x₀ * Real.exp (-h * t)) ^ 2 / 2
      = (h * x₀ ^ 2 / 2) * Real.exp (-2 * h * t) := by
  rw [mul_pow, sq (Real.exp (-h * t)), ← Real.exp_add]
  ring_nf

end SpectralPhysics.JointSAGF
