/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.F2FromSpectralAction.F2Identification
import SpectralPhysics.Cosmology.SigmaTrDispersion

/-!
# Connection: `f_2` from the Spectral Action  ↔  `f_2` in `SigmaTrDispersion`

The module `SpectralPhysics/Cosmology/SigmaTrDispersion.lean` carries a
concrete framework value

  `f_2 := 48 · e⁶`

with positivity `f2_pos : 0 < SpectralPhysics.Cosmology.f2`, and uses
it inside the SAGF trace-sector dispersion symbol
`σ_tr(ξ) = c₁ f_2 Λ² ξ² − 6 f_0 α_eff ξ⁴` of v0.9 §5.3.

This file connects:

  (Spectral action) `m.f_2` cutoff moment
  ─── via Chamseddine–Connes + Vassilevich (`f2_identification`) ───→
  (Framework) `SpectralPhysics.Cosmology.f2 = 48 · e⁶`.

The connection is **NOT** a derivation of the specific number `48·e⁶`
from the spectral action (that number is the *Connes–Marcolli per-mode
log-Yukawa* primitive, see `Cosmology/SigmaTrDispersion.lean:91`). It
is a *typing* statement: the `f_2` used in `σ_tr` is precisely the
`f_2` cutoff moment of the spectral action, and the identification
chain that puts that moment into the framework is the
Chamseddine–Connes + Vassilevich axiom-of-citation chain.

## Honest scope

* We carry the *match* between the abstract cutoff moment and the
  concrete framework value as a **predicate** on the spectral-action
  cutoff. The match holds *iff* the framework-internal value is the
  chosen cutoff moment.
* This is the analogue of `CutoffNormalization` in
  `SeeleyDeWitt/SpectralActionR2.lean` — an explicit *framework
  convention* exposed as a hypothesis, not a hidden axiom.

## References

* Chamseddine, A.H., Connes, A. (1997). *The spectral action principle.*
  Comm. Math. Phys. **186**, 731–750.
* Vassilevich, D.V. (2003). *Heat kernel expansion: user's manual.*
  Phys. Rept. **388**, 279–360.
* Ben-Shalom (2026). Spectral Physics v0.9.1, §5.3 (SAGF trace sector).
-/

namespace SpectralPhysics.F2FromSpectralAction

open SpectralPhysics.Cosmology

/-! ## The framework convention -/

/-- **Framework convention.**  A `SpectralActionCutoff` `m` is *aligned
    with* the framework-internal value of `f_2` in `SigmaTrDispersion`
    iff `m.f_2 = 48 · e^6` (the Connes–Marcolli per-mode log-Yukawa
    primitive).

    This is the explicit framework convention — equivalent in spirit
    to `CutoffNormalization` in `SeeleyDeWitt/SpectralActionR2.lean`.
    It is a *cutoff choice*, not a derivation. -/
def FrameworkAlignedCutoff (m : SpectralActionCutoff) : Prop :=
  m.f_2 = SpectralPhysics.Cosmology.f2

/-! ## The connection: under framework alignment, the spectral-action
    f_2 matches the framework f_2.

The connection here is intentionally weak: it states that the
spectral-action `f_2` cutoff moment, when chosen to match the
framework convention, equals the framework's `f_2`. The framework's
`f_2 = 48 · e^6` itself is a Connes–Marcolli primitive (see
`Cosmology/SigmaTrDispersion.lean:91`) and is NOT derived here. -/

/-- **Connection theorem.**  Given:

    * `h_cc : ChamseddineConnesExpansion m a2`  — CC 1997 §2.
    * `h_vass : VassilevichA2Coefficient a2`     — Vassilevich 2003 eq. 4.13.
    * `h_aligned : FrameworkAlignedCutoff m`     — framework convention
      `m.f_2 = 48 · e^6`.

    Then the spectral-action `f_2` (recovered from the Λ²-coefficient
    via `f2_identification`) equals the framework's `Cosmology.f2`. -/
theorem sigmaTr_f2_matches_spectral_action
    (m : SpectralActionCutoff) (a2 : A2Coefficient)
    (h_cc : ChamseddineConnesExpansion m a2)
    (h_vass : VassilevichA2Coefficient a2)
    (h_aligned : FrameworkAlignedCutoff m) :
    lambda2_coefficient m a2 / a2.value = SpectralPhysics.Cosmology.f2 := by
  -- Step 1: identify Λ²/a_2 with m.f_2 (the load-bearing theorem).
  have h_ident := f2_identification m a2 h_cc h_vass
  -- Step 2: framework alignment substitutes m.f_2 → Cosmology.f2.
  unfold FrameworkAlignedCutoff at h_aligned
  rw [h_ident, h_aligned]

/-- **Positivity of the framework `f_2` is preserved.**  Under the
    connection, the framework's `f_2_pos` is recovered.  This is the
    consistency check that the spectral-action identification respects
    the framework's standing positivity. -/
theorem sigmaTr_f2_pos_from_spectral_action
    (m : SpectralActionCutoff) (a2 : A2Coefficient)
    (_h_cc : ChamseddineConnesExpansion m a2)
    (_h_vass : VassilevichA2Coefficient a2)
    (h_aligned : FrameworkAlignedCutoff m) :
    0 < SpectralPhysics.Cosmology.f2 := by
  -- The framework f_2_pos is already a theorem in SigmaTrDispersion.
  -- We re-derive it through the connection to demonstrate the chain
  -- is *consumed*: removing `h_aligned` breaks the rewrite.
  rw [← h_aligned]
  exact m.f_2_pos

/-! ## Note on conventions

The framework's `f_2 = 48 · e^6` (`SigmaTrDispersion.lean:93`) carries
the Connes–Marcolli per-mode log-Yukawa normalization.  It is **NOT**
derived in this module; it is a Tier-2 primitive of the framework
documented inside `SigmaTrDispersion.lean` itself.

What this module *does* close:

1. The *typing* of `f_2`: it is the cutoff moment of the
   Chamseddine–Connes spectral action, paired with the Vassilevich
   `a_2` heat-kernel coefficient.
2. The *recovery* of `f_2` from the spectral-action `Λ²` coefficient
   by division by `a_2` (`f2_identification`).
3. The *consistency* between the abstract `f_2` and the framework's
   `48 · e^6` *under* the explicit `FrameworkAlignedCutoff`
   convention.

What this module **does not** close:

* The specific number `48 · e^6`. That is the Connes–Marcolli per-mode
  log-Yukawa primitive — see v0.9.1 §5.3 and the v0.9.2 deferred
  item D.3 for the broader derivation goal.
-/

end SpectralPhysics.F2FromSpectralAction
