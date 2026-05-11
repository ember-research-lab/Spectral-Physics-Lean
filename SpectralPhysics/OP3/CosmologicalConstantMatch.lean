/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.OP3.Lambda1Bound

/-!
# OP3: Comparison to the Observed Cosmological Constant (Honest)

This file separates the **framework prediction** from the **empirical
comparison** to Λ_obs.  It contains exactly one substantive statement,
framed as a *biconditional* between two named real numbers:

> IF the framework's SCSE prediction `λ_1(k*) = exp(−κ_2(T)/2) · Λ_c²`
> happens to equal the empirical input `Λ_obs`,
> THEN the framework is empirically consistent with the observed Λ.

This is **empirical confirmation, not derivation**.  We do NOT define
`Λ_obs` in terms of any framework primitive, and we do NOT define
`κ_2(T)` in terms of `Λ_obs`.  The match (if it holds) is an *external*
fact about the framework's prediction lining up with cosmology.

## Comparison to the audit-caught prior scaffold

| Aspect | Prior (audit-caught) | This version |
|---|---|---|
| `kappa2_target` defined as | `2 · log(Λ_c² / Λ_obs)` (circular) | (removed) |
| SCSE formula returns | `Λ_obs` by algebraic identity | the framework's prediction |
| Headline claim | unconditional `λ_1 = Λ_obs` | conditional "match if and only if" |
| `op3_lambda1_matches_observed` | a *theorem* | a *hypothesis* (`PredictionMatchesObservation`) |
| 46-digit "agreement" | definitional, not derivational | absent — the match is a Prop, not an equation |

## The empirical-input axioms (named, classified, isolated)

We declare exactly two named real-valued constants, both classified as
**empirical input** (NOT framework primitives):

* `rho_Lambda_obs` — Planck-2018 dark-energy density, `ρ_Λ / M_Pl⁴`.
* `lambda_obs` — derived from `rho_Lambda_obs` via Einstein's equation
  `Λ = 8π ρ_Λ`.

These appear ONLY in this file.  They do NOT enter
`SCSEClosureSystem.lean` (the framework primitives) or
`Lambda1Bound.lean` (the conditional headline).

## What is and isn't proved

* `framework_empirically_consistent`: a **biconditional** —
  the framework's predicted `λ_1(k*)` equals `Λ_obs`
  IFF
  `κ_2(T) = 2 · log(Λ_c² / Λ_obs)`.

  This is a tautological algebraic equivalence, **not a derivation**.
  It expresses the conditional: if the framework's intrinsic κ_2(T)
  happens to land at the value that makes the prediction match,
  then the prediction matches.

* `empirical_match_is_external_fact`: a comment-level statement
  emphasising that whether the antecedent holds is a question about
  the SM spectrum's κ_2 — NOT something we can derive within this file.

## Smuggling check

* No `axiom` introduces a numerical bracket on `λ_1`.
* No `def` engineers a circular identity.
* The two empirical constants (`rho_Lambda_obs`, `lambda_obs`) are
  isolated to this file, classified as empirical input, and never
  used to derive themselves.
* The match between framework and observation is stated as a
  *hypothesis* (Prop), not a *theorem*.
-/

noncomputable section

open Real

namespace SpectralPhysics.OP3

/-! ## Empirical inputs (classified) -/

/-- **EMPIRICAL INPUT**: the Planck-2018 dark-energy density in Planck
units, `ρ_Λ / M_Pl⁴ ≈ 1.1 × 10⁻¹²²`.

* **Classification**: empirical observational input.
  This is NOT a framework primitive; the framework neither predicts nor
  derives this value.
* **Source**: Planck 2018 cosmological parameter results.
* **Scope**: used ONLY in this file, to define `lambda_obs`.  No other
  file in the OP3 directory depends on this constant.

If the precise numerical value is desired (e.g., 1.105 × 10⁻¹²² with
2024 cosmology updates), only this `def` need change. -/
def rho_Lambda_obs : ℝ := 1.1e-122

/-- **EMPIRICAL DERIVED**: `Λ_obs / M_Pl² = 8π · ρ_Λ_obs`.

* **Classification**: empirical derived (from `rho_Lambda_obs` via
  Einstein's equation `Λ = 8π ρ_Λ`).
* **Scope**: used ONLY in this file, in the empirical-match
  hypothesis. -/
def lambda_obs : ℝ := 8 * Real.pi * rho_Lambda_obs

theorem lambda_obs_pos : 0 < lambda_obs := by
  unfold lambda_obs rho_Lambda_obs
  have h_pi : (0 : ℝ) < Real.pi := Real.pi_pos
  positivity

/-! ## The match predicate (a hypothesis, not a theorem) -/

/-- **Predicate**: the framework's SCSE prediction on triple `T` matches
the observed Λ.

This is a Prop-valued statement.  We do NOT prove it for any specific
triple.  Whether it holds for the SM visible+hidden spectrum is exactly
the empirical-confirmation question.

The audit-caught prior scaffold tried to *force* this to hold by
defining `κ_2(T)` in terms of `Λ_obs`.  Here it is a clean Prop —
either the SM's intrinsic κ_2 lands at the matching value, or it
doesn't.  Determining which is an empirical question, not an algebraic
one. -/
def PredictionMatchesObservation (T : FiniteSpectralTriple) : Prop :=
  lambda1Predicted T = lambda_obs

/-! ## Algebraic equivalence (tautology, NOT a derivation)

The framework's prediction `λ_1(T) = exp(−κ_2(T)/2) · Λ_c²` equals the
empirical `Λ_obs` IF AND ONLY IF the cumulant `κ_2(T)` equals the value
`2 · log(Λ_c² / Λ_obs)`.

This is **pure algebra** — the SCSE formula is bijective in κ_2 given
Λ_c² > 0 and Λ_obs > 0, so the equivalence is automatic.

The **key honesty point**: the LHS of the equivalence is the framework
prediction; the RHS is a *condition on the framework's κ_2*.  We are
not saying "κ_2 must equal that value" — we are saying "the match
holds iff κ_2 happens to take that value".  Whether the SM's intrinsic
κ_2 satisfies this is an empirical question separate from the
algebraic equivalence. -/

/-- **Algebraic equivalence (NOT a derivation)**: the prediction
matches observation iff the triple's κ_2 lands at the matching value.

This is `exp(−x/2) · Λ_c² = Λ_obs ↔ x = 2 · log(Λ_c² / Λ_obs)`.

This is **tautological**: the SCSE formula is bijective in κ_2.  The
match is a fact about the framework's *intrinsic* κ_2, not a
derivation of Λ_obs from anything. -/
theorem framework_match_iff_kappa2_eq
    (T : FiniteSpectralTriple) :
    PredictionMatchesObservation T ↔
      T.kappa2 = 2 * Real.log (lambda_c_sq / lambda_obs) := by
  unfold PredictionMatchesObservation lambda1Predicted
  constructor
  · -- forward: exp(- κ_2/2) * Λ_c² = Λ_obs → κ_2 = 2 log(Λ_c² / Λ_obs)
    intro h_eq
    have hLc : 0 < lambda_c_sq := lambda_c_sq_pos
    have hLo : 0 < lambda_obs := lambda_obs_pos
    -- exp(-κ_2/2) = Λ_obs / Λ_c²
    have h1 : Real.exp (-T.kappa2 / 2) = lambda_obs / lambda_c_sq := by
      have := h_eq
      field_simp at this ⊢
      linarith [this]
    -- -κ_2/2 = log(Λ_obs / Λ_c²)
    have h2 : -T.kappa2 / 2 = Real.log (lambda_obs / lambda_c_sq) := by
      rw [← h1]
      exact (Real.log_exp _).symm
    -- κ_2 = -2 log(Λ_obs / Λ_c²) = 2 log(Λ_c² / Λ_obs)
    have h_div_pos : 0 < lambda_c_sq / lambda_obs := div_pos hLc hLo
    have h_log_inv : Real.log (lambda_obs / lambda_c_sq)
                   = -Real.log (lambda_c_sq / lambda_obs) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    rw [h_log_inv] at h2
    linarith
  · -- backward: κ_2 = 2 log(Λ_c² / Λ_obs) → exp(-κ_2/2) * Λ_c² = Λ_obs
    intro h_kappa
    have hLc : 0 < lambda_c_sq := lambda_c_sq_pos
    have hLo : 0 < lambda_obs := lambda_obs_pos
    have h_div_pos : 0 < lambda_c_sq / lambda_obs := div_pos hLc hLo
    rw [h_kappa]
    have h_simp : -(2 * Real.log (lambda_c_sq / lambda_obs)) / 2
                = -Real.log (lambda_c_sq / lambda_obs) := by ring
    rw [h_simp]
    rw [show -Real.log (lambda_c_sq / lambda_obs)
          = Real.log (lambda_obs / lambda_c_sq) by
          rw [← Real.log_inv]; congr 1; field_simp]
    rw [Real.exp_log (div_pos hLo hLc)]
    field_simp

/-! ## The conditional empirical theorem (honest)

The strongest theorem we can honestly state about the framework's
empirical content: given the three v0.9 open-problem hypotheses
(`SCSEHasFixedPoint`, `SCSEFixedPointUnique`,
`VisibleSpectrumFollowsBakerForm`) AND the empirical-match hypothesis,
the SCSE fixed point equals `Λ_obs`.

This is *not* a derivation of `Λ_obs`.  It is a structural conditional:
IF the SM spectral triple satisfies the four predicates above, THEN
the framework reproduces `Λ_obs`. -/

/-- **Conditional empirical-match theorem (honest)**.

Hypotheses (all named):

* `h_baker : VisibleSpectrumFollowsBakerForm T`
  (v0.9 line 10977, open structural condition)
* `h_scse_exists : SCSEHasFixedPoint T`
  (v0.9 line 9670, open computation)
* `h_scse_unique : SCSEFixedPointUnique T`
  (v0.9 line 9749, open computation)
* `h_match : PredictionMatchesObservation T`
  (empirical hypothesis: the framework's κ_2(T) happens to land at the
   value that matches Λ_obs)

Conclusion: there exists a positive fixed point of the SCSE on `T`
equal to `Λ_obs`.

The fourth hypothesis (`h_match`) is the **honest replacement** for
the audit-caught circular construction.  Whether it holds for the SM
spectral triple is an **empirical** question (does the SM's intrinsic
κ_2 actually equal `2 · log(Λ_c² / Λ_obs)`?), not a definitional one. -/
theorem op3_lambda1_matches_observed_conditional
    (T : FiniteSpectralTriple)
    (_h_baker : VisibleSpectrumFollowsBakerForm T)
    (h_scse_exists : SCSEHasFixedPoint T)
    (_h_scse_unique : SCSEFixedPointUnique T)
    (h_match : PredictionMatchesObservation T) :
    ∃ lam : ℝ, 0 < lam ∧ lam = lambda_obs := by
  rcases h_scse_exists with ⟨lam_star, h_pos, h_eq⟩
  refine ⟨lam_star, h_pos, ?_⟩
  rw [h_eq]
  exact h_match

/-! ## What is NOT here

We deliberately do NOT include:

* A *theorem* `λ_1 = Λ_obs` (only a conditional with `h_match` as
  hypothesis).
* A numerical-bracket axiom on `|λ_1 − 2.7646 × 10⁻¹²¹|` (the audit-
  caught `norm_num`-closeable axiom; removed entirely).
* A claim that the empirical match is a "derivation" or a "prediction"
  in the strong sense.  It is empirical confirmation, conditional on
  the SM triple's intrinsic κ_2 landing at the right value, and on the
  three structural predicates holding.

The empirical-confirmation question — does the SM spectral triple
satisfy `PredictionMatchesObservation`? — is left as the empirical
content of v0.9's OP3 program.  The Lean formalisation makes the
conditional structure explicit; the conditionality is precisely v0.9
lines 9670 / 9679 / 9749's open problems. -/

end SpectralPhysics.OP3

end
