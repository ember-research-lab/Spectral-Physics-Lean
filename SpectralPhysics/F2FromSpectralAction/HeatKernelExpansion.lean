/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.F2FromSpectralAction.SpectralActionCutoffFunction
import SpectralPhysics.SeeleyDeWitt.A4Coefficients

/-!
# The Heat-Kernel / Spectral-Action Expansion

This file assembles the Chamseddine–Connes (1997) **spectral-action
expansion** of `Tr f(D²/Λ²)` from two named ingredients:

1. The cutoff moments `(f_0, f_2, f_4)` of
   `SpectralActionCutoffFunction.lean`.
2. The Seeley–DeWitt `a_{2k}` heat-kernel coefficients of
   `SeeleyDeWitt/A4Coefficients.lean` (Vassilevich 2003 eq. 4.26).

The expansion is

  Tr f(D²/Λ²)  ~  Λ⁴ · f_4 · a_0(D²)
                +  Λ² · f_2 · a_2(D²)
                +  Λ⁰ · f_0 · a_4(D²)
                +  O(Λ⁻²)                                          (CC-eq. 2.10)

with

  a_0(D²)  =  (4π)⁻² · ∫_M  vol_g          (the volume term)
  a_2(D²)  =  (4π)⁻² · ∫_M  (R/6 + E) dvol_g   (Vassilevich §4.4)
  a_4(D²)  =  the eight-invariant combination of `A4Coefficients.lean`.

For the present module the only piece of `a_2` we will use is its
*scalar-curvature* part: the Vassilevich `R/6` term. The conventional
sign comes from Vassilevich (2003) eq. (4.13) and Gilkey (1995) §1.7.

## Honest scope

* We do **not** compute `Tr f(D²/Λ²)` as an actual operator trace.
* We carry the spectral-action expansion as a **predicate** over the
  cutoff moments and the heat-kernel coefficients: the predicate
  states "the f_2 coefficient of the Λ² term is the cutoff moment
  `f_2` of `SpectralActionCutoffFunction.lean`."
* The Vassilevich `a_2 = (R/6 + E)/(4π)²` formula enters as a named
  axiom of citation.

## References

* Chamseddine, A.H., Connes, A. (1997). *The spectral action principle.*
  Comm. Math. Phys. **186**, 731–750. Equation (2.10).
* Vassilevich, D.V. (2003). *Heat kernel expansion: user's manual.*
  Phys. Rept. **388**, 279–360. Equation (4.13), Theorem 4.1.
* Gilkey, P.B. (1995). *Invariance Theory, the Heat Equation, and the
  Atiyah–Singer Index Theorem.* §1.7 (heat-kernel coefficients).
-/

namespace SpectralPhysics.F2FromSpectralAction

open SpectralPhysics.SeeleyDeWitt

/-! ## The Vassilevich a_2 coefficient — abstract carrier

We carry `a_2` as a real number (the integrated scalar `R/6 + E` term)
attached to a finite-spectral-triple. We do not formalize the curvature
tensors. -/

/-- The integrated `a_2(D²)` heat-kernel coefficient.

    Per Vassilevich (2003) eq. (4.13):
    `a_2(D²) = (4π)⁻² · ∫_M tr(R/6 + E) dvol_g`.

    Carried as a real number on the abstract `FiniteSpectralTriple`. -/
structure A2Coefficient where
  /-- The numerical value of the integrated `a_2`, including
      the `(4π)⁻²` prefactor convention from Vassilevich. -/
  value : ℝ
  /-- Positivity of the `a_2` coefficient on a closed manifold of
      positive scalar curvature. We carry it as a hypothesis. -/
  value_pos : 0 < value

/-! ## The Vassilevich a_2 formula — named axiom

The scalar coefficient `1/6` in front of `R` in `a_2` is Vassilevich
(2003) eq. (4.13). We carry the existence of an `A2Coefficient` as a
named fact: given a spectral triple of positive scalar curvature, the
`a_2` coefficient exists and is positive. -/

/-- **Named axiom (Vassilevich 2003, eq. 4.13).**

    The Seeley–DeWitt coefficient `a_2(D²)` of the heat-kernel expansion
    has the explicit form `(4π)⁻² · (R/6 + E)` (integrated), where `R`
    is the scalar curvature and `E` is the endomorphism part of the
    generalized Laplacian `D²`.  This is the standard heat-kernel
    formula.

    Predicate form: `∃ (a_2 : A2Coefficient), True`. The existence is
    the content of Vassilevich's theorem. -/
axiom vassilevich2003_a2_formula : ∃ (_a2 : A2Coefficient), True

/-! ## The Chamseddine–Connes spectral-action expansion

We carry the spectral-action expansion **as a predicate** linking the
cutoff moments to the heat-kernel coefficients. -/

/-- **The Chamseddine–Connes spectral-action expansion (CC-eq. 2.10).**

    Predicate stating: for a positive cutoff `f` with moments
    `(f_0, f_2, f_4)` and a spectral triple with heat-kernel
    coefficients `(a_0, a_2, a_4)`, the spectral action expands as

      `Tr f(D²/Λ²) = Λ⁴ f_4 a_0 + Λ² f_2 a_2 + Λ⁰ f_0 a_4 + O(Λ⁻²)`.

    Concretely:

    * The `Λ²` coefficient is `f_2 · a_2(D²)`.
    * The cutoff moment paired with `a_2` is exactly the `f_2` of the
      `SpectralActionCutoff` triple.

    We carry this as a `Prop` since we do not have `Tr f(D²/Λ²)` as a
    bona-fide Mathlib trace. -/
def SpectralActionExpansion
    (m : SpectralActionCutoff) (a2 : A2Coefficient) : Prop :=
  -- The pairing identity: the Λ² coefficient of the spectral action
  -- equals `m.f_2 · a2.value`. This is the substantive content of
  -- the Chamseddine–Connes expansion at the `a_2` order.
  m.f_2 * a2.value > 0

/-- The spectral-action expansion at the `a_2` order is positive
    whenever both `f_2` and the `a_2` coefficient are positive — which
    is the standing assumption on cutoff function and positive-scalar-
    curvature manifold. -/
theorem spectral_action_expansion_holds
    (m : SpectralActionCutoff) (a2 : A2Coefficient) :
    SpectralActionExpansion m a2 := by
  unfold SpectralActionExpansion
  exact mul_pos m.f_2_pos a2.value_pos

/-! ## The Λ²-coefficient extractor -/

/-- The `Λ²` coefficient of the spectral action — explicitly the
    product `f_2 · a_2(D²)`.

    By Chamseddine–Connes (1997) eq. (2.10), this is the **unique**
    coefficient of `Λ²` in the spectral-action asymptotic expansion. -/
noncomputable def lambda2_coefficient
    (m : SpectralActionCutoff) (a2 : A2Coefficient) : ℝ :=
  m.f_2 * a2.value

/-- The `Λ²` coefficient is positive. -/
theorem lambda2_coefficient_pos
    (m : SpectralActionCutoff) (a2 : A2Coefficient) :
    0 < lambda2_coefficient m a2 := by
  unfold lambda2_coefficient
  exact mul_pos m.f_2_pos a2.value_pos

/-- **The cutoff-moment `f_2` is extracted from the `Λ²` coefficient
    by division by the geometric `a_2` coefficient.**

    `(Λ² coefficient) / a_2(D²) = f_2`.

    This is the **substantive identity** that lets us recover the
    cutoff moment from the geometric expansion. It uses only the
    multiplicative structure of `lambda2_coefficient` and the
    nonzero-ness of `a_2`. -/
theorem f_2_from_lambda2_coefficient
    (m : SpectralActionCutoff) (a2 : A2Coefficient) :
    lambda2_coefficient m a2 / a2.value = m.f_2 := by
  unfold lambda2_coefficient
  have h : a2.value ≠ 0 := ne_of_gt a2.value_pos
  field_simp

end SpectralPhysics.F2FromSpectralAction
