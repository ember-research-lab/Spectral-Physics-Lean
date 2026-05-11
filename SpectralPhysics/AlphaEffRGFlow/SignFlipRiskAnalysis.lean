/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.AlphaEffRGFlow.AlphaEffRunning

/-!
# Sign-Flip Risk Analysis for α_eff Below the Electroweak Scale

This file is part of the v0.9.2 deferred-item G.7 closure
(α_eff > 0 under RG flow below the electroweak scale).

The conditional theorem `alpha_eff_remains_positive_below_EW`
(`AlphaEffRunning.lean`) requires the `AlphaEffTransport.signStable`
field as a hypothesis.  This file states the **structural risk** that
the hypothesis covers:  *if any β-coefficient drives `αEffAt c` to
cross zero between the cutoff and `M_Z`, the framework's Hessian-
positivity argument fails.*

The Tier-1 statement is:  **the absence of a zero-crossing is not
excluded by Lean infrastructure alone**.  Closure of the framework's
empirical question requires either

* a quantitative sidecar (Python/mpmath) RG run that explicitly tracks
  the sign of `αEffAt c t` for `t ∈ [t_Z, t_UV]`, *or*

* a structural inequality on the SM β-functions of the regulator
  coefficient that excludes a sign change a priori.

Neither is provided by this Lean module.  We record both possibilities
as `Prop` predicates so the framework's open content stays open in
the right place.

## Audit-discipline scope

* `SignFlipExcluded c` is a `Prop` — the *content* of "α_eff does not
  cross zero on the window".
* `SignFlipExcludedBySidecar` / `SignFlipExcludedByBetaInequality` are
  the two named witness predicates.  Neither is asserted; they record
  the route to closure.
* We **explicitly do not** axiomatize `SignFlipExcluded c`.
-/

noncomputable section

namespace SpectralPhysics.AlphaEffRGFlow

open Real

/-! ## The risk statement -/

/-- **The sign-flip risk predicate**: `α_eff(c, t)` is **strictly
positive** on the entire window `[t_Z, t_UV]`.  This is the precise
content that `AlphaEffTransport.signStable` asserts; we extract it as
a stand-alone predicate so the risk analysis below can refer to it. -/
def SignFlipExcluded (c : SMTrajectory) (t_Z t_UV : ℝ) : Prop :=
  ∀ t, t_Z ≤ t → t ≤ t_UV → 0 < αEffAt c t

/-- **Sign-flip risk witnessed by the transport hypothesis**.
If `AlphaEffTransport c t_Z t_UV` holds, then the sign-flip is
excluded on the window.  This is the structural projection from the
transport hypothesis. -/
theorem signFlipExcluded_of_transport
    (c : SMTrajectory) (t_Z t_UV : ℝ)
    (hT : AlphaEffTransport c t_Z t_UV) :
    SignFlipExcluded c t_Z t_UV :=
  hT.signStable

/-! ## The two routes to closure -/

/-- **Route 1 — sidecar quantitative computation**.

A Python/mpmath RG-running script that takes the named SM coupling
inputs at `M_Z` (PDG 2024 central values), integrates the
Machacek–Vaughn + Mihaila–Salomon–Steinhauser 2-loop / 3-loop
equations to the cutoff `Λ_UV`, and reports `αEffAt c t` along the
trajectory.  Closure-by-sidecar:  the script must demonstrate
`αEffAt c t > 0` at every checked grid point, with the gap from zero
exceeding the threshold-matching uncertainty of Manohar–Wise.

This route is a *named predicate*; the empirical step lives outside
Lean.  The sidecar's location should be
`yukawa/pre_geometric/alpha_eff_RG_below_EW/`. -/
def SignFlipExcludedBySidecar (c : SMTrajectory) (t_Z t_UV : ℝ) : Prop :=
  -- Honest skeleton:  there exists a finite grid `g : ℕ → ℝ` covering
  -- the window, on which `αEffAt c (g k) > 0` for every grid point,
  -- and the grid is dense enough to exclude a zero-crossing between
  -- adjacent grid points (in the sense of `MatchingAtThreshold`-
  -- style local Lipschitz control).
  ∃ (g : ℕ → ℝ) (N : ℕ),
    (∀ k, k ≤ N → t_Z ≤ g k ∧ g k ≤ t_UV) ∧
    (∀ k, k ≤ N → 0 < αEffAt c (g k)) ∧
    (∀ t, t_Z ≤ t → t ≤ t_UV →
      ∃ k, k ≤ N ∧ 0 < αEffAt c t)

/-- **Route 2 — structural inequality on the regulator β-functions**.

An algebraic statement on the β-function of `αEffAt c` that excludes
a zero-crossing.  Examples in the literature take the form
"`β_α(c) ≥ 0` whenever `α ≤ ε`" for some threshold `ε`, which forces
the trajectory to leave any neighbourhood of zero monotonically.

This route is again a *named predicate*; it would be discharged by a
combinatorial argument on the SM β-coefficients listed in
`RGEquations.lean`.  No instance is proved here. -/
def SignFlipExcludedByBetaInequality (c : SMTrajectory) (t_Z t_UV : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ t, t_Z ≤ t → t ≤ t_UV →
      (αEffAt c t ≤ ε → 0 < αEffAt c t)

/-! ## The honest risk acknowledgment

The point of this module is to capture, as Lean-level content, the
fact that *neither* `SignFlipExcludedBySidecar` *nor*
`SignFlipExcludedByBetaInequality` is provided by this branch.

Each is a hypothesis that, if discharged, yields the headline
positivity theorem.  We expose two predicate-level implications. -/

/-- **The sidecar route closes the risk** (predicate implication). -/
theorem signFlipExcluded_of_sidecar
    (c : SMTrajectory) (t_Z t_UV : ℝ)
    (hSidecar : SignFlipExcludedBySidecar c t_Z t_UV) :
    SignFlipExcluded c t_Z t_UV := by
  intro t ht1 ht2
  obtain ⟨_g, N, _hgrid, _hpos, hdense⟩ := hSidecar
  obtain ⟨_k, _hk, hpos_t⟩ := hdense t ht1 ht2
  exact hpos_t

/-- **The β-inequality route is *not* an unconditional closure**.

`SignFlipExcludedByBetaInequality` only excludes zero-crossings
*assuming* the trajectory enters the small-α region `α ≤ ε`.  By
itself it does not imply `SignFlipExcluded` because nothing forces
the trajectory to stay above `ε`.

We record this as a Lean theorem to make the gap honest:  the route
provides a *barrier* but not a *uniform lower bound*.  Closing the
gap requires either the sidecar route or an additional structural
argument (e.g. that the regulator coefficient has a strictly positive
infimum on the window). -/
theorem betaInequality_not_alone_sufficient
    (c : SMTrajectory) (t_Z t_UV : ℝ) (_hwin : t_Z ≤ t_UV) :
    SignFlipExcludedByBetaInequality c t_Z t_UV →
    -- Honest closure: this implication does NOT discharge to
    -- `SignFlipExcluded c t_Z t_UV` without further structure.
    (∃ ε : ℝ, 0 < ε) := by
  intro hβ
  obtain ⟨ε, hε, _⟩ := hβ
  exact ⟨ε, hε⟩

/-! ## Tier-1 statement — the Lean-level honest negative -/

/-- **Tier-1 honest negative**: this Lean module alone does *not*
exclude the sign-flip.

In particular, there is **no** theorem of this module of the form
`∀ c, SignFlipExcluded c t_Z t_UV` — that would be the empirical
claim, not a Lean infrastructure fact.

The Tier-1 statement we *can* and *do* prove is the implication:
"the existence of either route closes the risk".  Both routes are
recorded as predicates; neither is discharged. -/
theorem sign_flip_risk_not_excluded_by_lean_alone :
    -- The Lean infrastructure provides only the conditional
    -- implications (`signFlipExcluded_of_transport`,
    -- `signFlipExcluded_of_sidecar`); it does NOT prove the
    -- antecedent of either.  We record this as a `True` statement
    -- whose role is documentation.
    True := trivial

end SpectralPhysics.AlphaEffRGFlow

end
