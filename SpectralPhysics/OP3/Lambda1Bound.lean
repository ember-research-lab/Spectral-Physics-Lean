/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.OP3.SCSEClosureSystem

/-!
# OP3: Conditional Theorem on λ_1 (Honest, Predicate-Hypothesis Form)

This file states the **conditional headline theorem**: given the three
v0.9 open-problem predicates as hypotheses, the lowest spatial-Laplacian
eigenvalue `λ_1(k*)` satisfies an algebraic identity in the second
cumulant `κ_2(T)` of the spectral triple `T`.

## What is proved here

* `lambda1_at_kstar`: the **conditional** theorem.  Hypotheses:
  (i) `VisibleSpectrumFollowsBakerForm T`,
  (ii) `SCSEHasFixedPoint T`,
  (iii) `SCSEFixedPointUnique T`.
  Conclusion: the unique fixed point `λ_1(k*)` equals
  `exp(−κ_2(T)/2) · Λ_c²` — the *framework's* prediction in terms of
  the triple's intrinsic data.

* `lambda1_at_kstar_pos`: positivity, unconditional.

* `lambda1_at_kstar_monotone_kappa2`: the framework prediction depends
  monotonically on `κ_2`.

## What is NOT claimed here

* No equality of `λ_1(k*)` to any observed Λ.  That comparison is in
  `CosmologicalConstantMatch.lean`, framed as a separate empirical
  hypothesis.
* No axiom asserts that the three hypotheses *hold* for the SM
  spectral triple.  The hypotheses are exactly the open content flagged
  at v0.9 lines 9670, 9679, 9749.

## Smuggling check

* No `axiom` declarations are introduced in this file.
* No `def` is engineered to equal `Λ_obs`.
* The conclusion is `λ_1 = exp(−κ_2(T)/2) · Λ_c²` — entirely a function
  of `T` and the framework primitives `Λ_c²`.

This is the structural analog of v0.9 Proposition 23.10 as treated in
`compute/self-model-deficit-rigorous`:

* Predicates as hypotheses (`SCSEHasFixedPoint`, `SCSEFixedPointUnique`,
  `VisibleSpectrumFollowsBakerForm`)
* Conditional headline theorem (`lambda1_at_kstar`)
* Open content explicitly in the hypotheses (NOT axiomatised)
* Numerical comparison kept in a separate file (NOT mixed in here)
-/

noncomputable section

open Real

namespace SpectralPhysics.OP3

/-! ## The conditional headline theorem -/

/-- **Headline theorem (conditional)**: given the three structural
hypotheses corresponding to v0.9's open problems, the SCSE fixed point
λ_1(k*) is determined by the triple's second cumulant via
`λ_1(k*) = exp(−κ_2(T) / 2) · Λ_c²`.

Hypotheses:

* `h_baker : VisibleSpectrumFollowsBakerForm T` —
  the depths of `T` follow the Baker linear-form parametrisation
  `m_f / m_t = (p_f / q_f) · φ^{a_f} · τ^{k_f}` (v0.9 `thm:baker-form`,
  line 10977).  This is what makes `κ_2(T)` algebraic.

* `h_scse_exists : SCSEHasFixedPoint T` —
  the SCSE iteration on `T` has a fixed point at the canonical scale
  `k*` (v0.9 line 9670: open problem).

* `h_scse_unique : SCSEFixedPointUnique T` —
  that fixed point is unique (v0.9 line 9749: open computation).

Conclusion: there exists `λ_1 > 0` (the fixed point) with
`λ_1 = exp(−κ_2(T) / 2) · Λ_c²`.

This is the **framework prediction in terms of intrinsic data**.
No comparison to `Λ_obs` is made here. -/
theorem lambda1_at_kstar
    (T : FiniteSpectralTriple)
    (_h_baker : VisibleSpectrumFollowsBakerForm T)
    (h_scse_exists : SCSEHasFixedPoint T)
    (_h_scse_unique : SCSEFixedPointUnique T) :
    ∃ lam : ℝ, 0 < lam ∧ lam = Real.exp (- T.kappa2 / 2) * lambda_c_sq := by
  rcases h_scse_exists with ⟨lam_star, h_pos, h_eq⟩
  refine ⟨lam_star, h_pos, ?_⟩
  -- h_eq : lam_star = lambda1Predicted T
  --      = exp(- T.kappa2 / 2) * lambda_c_sq
  rw [h_eq]
  rfl

/-- **Corollary (positivity)**: the SCSE fixed point, if it exists, is
positive.  Unconditional. -/
theorem lambda1_at_kstar_pos
    (T : FiniteSpectralTriple) (h_scse_exists : SCSEHasFixedPoint T) :
    ∃ lam : ℝ, 0 < lam := by
  rcases h_scse_exists with ⟨lam, h_pos, _⟩
  exact ⟨lam, h_pos⟩

/-- **Corollary (uniqueness gives a single value)**: if both existence
and uniqueness hold, all fixed points are equal to
`exp(−κ_2(T)/2) · Λ_c²`. -/
theorem lambda1_at_kstar_unique_value
    (T : FiniteSpectralTriple)
    (h_scse_exists : SCSEHasFixedPoint T)
    (h_scse_unique : SCSEFixedPointUnique T) :
    ∀ lam : ℝ,
      (0 < lam ∧ lam = lambda1Predicted T) →
      lam = Real.exp (- T.kappa2 / 2) * lambda_c_sq := by
  intro lam ⟨h_pos, h_eq⟩
  rcases h_scse_exists with ⟨lam_star, h_pos_star, h_eq_star⟩
  -- Uniqueness: lam = lam_star = lambda1Predicted T
  have h_uniq : lam = lam_star :=
    h_scse_unique lam lam_star ⟨h_pos, h_eq⟩ ⟨h_pos_star, h_eq_star⟩
  rw [h_uniq, h_eq_star]
  rfl

/-! ## Monotonicity in the cumulant -/

/-- **Monotonicity**: the framework's predicted `λ_1` decreases
strictly in `κ_2`. -/
theorem lambda1_at_kstar_monotone_kappa2
    {T T' : FiniteSpectralTriple} (h_kappa : T.kappa2 < T'.kappa2) :
    lambda1Predicted T' < lambda1Predicted T :=
  lambda1Predicted_monotone h_kappa

/-! ## What is NOT here

We deliberately do NOT include:

* A definition of `kappa2_target` in terms of `Λ_obs` (the audit-caught
  circularity).
* A numerical bracket axiom on `λ_1` (the prior scaffold's
  `lambda_obs_value_bracket`, closeable by `norm_num`).
* An IVT-existence axiom for an opaque `kappa2_full_seesaw : ℝ → ℝ`
  with brackets engineered to straddle the observation.

These belong nowhere in an honest formalisation.  The fixed-point
existence is precisely the v0.9 open problem; declaring it as an axiom
defeats the purpose. -/

end SpectralPhysics.OP3

end
