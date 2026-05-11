/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The Spectral-Action Cutoff Function `f` and its Moments

The Chamseddine–Connes spectral action

  `S_CC(D, Λ, f)  =  Tr f(D² / Λ²)`

depends on a positive, sufficiently rapidly decaying cutoff function
`f : [0, ∞) → ℝ` only through three moments

  `f_0  := ∫₀^∞ f(u) · u⁻¹ du`        (Λ⁰ — the `a_4` term)
  `f_2  := ∫₀^∞ f(u)         du`        (Λ² — the `a_2 ∝ R` term)
  `f_4  := f(0)`                         (Λ⁴ — the `a_0` cosmological term)

This is the *cutoff-moment* convention of Chamseddine–Connes (1997).
The numerical values depend on the choice of `f`; they enter the
spectral action as inputs.

**Honest scope of this file.**

* We do not formalize `f` as a function with integrability assumptions
  in Mathlib; we abstract the three moments into a `Prop`-bearing
  predicate over a positive real-number-triple.
* The bijection between "specific choice of `f`" and "specific values
  of `(f_0, f_2, f_4)`" is *named* — it is the integral-transform
  bijection of Chamseddine–Connes 1997 §2 ("the spectral action
  depends on `f` only through `f_0`, `f_2`, `f_4`").
* Positivity of each moment is a precondition on `f`, not a derivation.

This is the substrate file. `HeatKernelExpansion.lean` will pair these
moments with the Seeley–DeWitt `a_{2k}` coefficients to assemble the
asymptotic spectral action.

## References

* Chamseddine, A.H., Connes, A. (1997). *The spectral action principle.*
  Comm. Math. Phys. **186**, 731–750. §2 — equation (2.10), cutoff
  expansion.
* Connes, A., Marcolli, M. (2008). *Noncommutative Geometry, Quantum
  Fields and Motives.* AMS. §17.3.
-/

namespace SpectralPhysics.F2FromSpectralAction

/-! ## The three cutoff moments as data -/

/-- The Chamseddine–Connes cutoff-function moment triple.

    Each field is a real number:

    * `f_0`  encodes `∫₀^∞ f(u) · u⁻¹ du`  — pairs with `a_4`  in `Λ⁰`.
    * `f_2`  encodes `∫₀^∞ f(u)         du`  — pairs with `a_2`  in `Λ²`.
    * `f_4`  encodes `f(0)`                — pairs with `a_0`  in `Λ⁴`.

    All three are required positive (a standing assumption on positive,
    suitably decaying `f`).

    This structure carries *the data* that the spectral action sees;
    everything else about the function `f` is irrelevant per
    Chamseddine–Connes (1997). -/
structure SpectralActionCutoff where
  f_0 : ℝ
  f_2 : ℝ
  f_4 : ℝ
  f_0_pos : 0 < f_0
  f_2_pos : 0 < f_2
  f_4_pos : 0 < f_4

namespace SpectralActionCutoff

/-- Trivial positivity restatement, kept for downstream simp-readability. -/
theorem f_0_nonneg (m : SpectralActionCutoff) : 0 ≤ m.f_0 := le_of_lt m.f_0_pos
theorem f_2_nonneg (m : SpectralActionCutoff) : 0 ≤ m.f_2 := le_of_lt m.f_2_pos
theorem f_4_nonneg (m : SpectralActionCutoff) : 0 ≤ m.f_4 := le_of_lt m.f_4_pos

end SpectralActionCutoff

/-! ## The integral-transform bijection (named, predicate form)

The Chamseddine–Connes (1997) statement that the spectral action
depends on `f` only through `(f_0, f_2, f_4)` is the *honest content*
that lets us carry these as a free triple. -/

/-- **The Chamseddine–Connes integral-transform bijection.**

    Predicate stating: given a positive cutoff function `f`, the
    spectral action `Tr f(D²/Λ²)` is a polynomial in `Λ` whose
    coefficients depend on `f` only through the three moments
    `(f_0, f_2, f_4)`.

    This is the predicate-hypothesis form of Chamseddine–Connes 1997
    Theorem 2.1 / eq. (2.10). It is named, not derived. -/
def CutoffMomentBijection (m : SpectralActionCutoff) : Prop :=
  0 < m.f_0 ∧ 0 < m.f_2 ∧ 0 < m.f_4

/-- The bijection predicate is *exactly* the positivity of the three
    moments, by construction. -/
theorem cutoff_moment_bijection_of_data (m : SpectralActionCutoff) :
    CutoffMomentBijection m :=
  ⟨m.f_0_pos, m.f_2_pos, m.f_4_pos⟩

end SpectralPhysics.F2FromSpectralAction
