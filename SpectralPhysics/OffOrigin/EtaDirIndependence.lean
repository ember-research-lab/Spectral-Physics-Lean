/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta

/-!
# eta_dir independence — Phase 3 scaffold (grounded on the rigorous deficit infra)

Reuses `VisibleSpectrum` / `informationContent` from `SelfModelDeficitRigorous.SpectralZeta`
(the even / M1 deficit `-ζ̃'(0)_vis = Σ mult·(-log y)`), so the blindness lemma below applies
to the framework's actual spectral functional, not a toy.

STATUS (do NOT upgrade without an adversarial audit: vacuity check + `#print axioms`):
- `spectral_functional_M2_invariant`, `informationContent_M2_invariant` : **CLOSED given the
  hypothesis** `frozen` (a pure-M2 deformation fixes the visible eigenvalue spectrum). The
  remaining work is to *derive* `frozen` from non-normal operator theory (numerical range /
  nilpotent-in-eigenbasis) — verdict for that operator-theoretic statement: **OPEN**.
- `forward_origin` : **OPEN** (`sorry`). Phase 1 = BACK-SOLVE, Phase 2 = FREE: no spectral
  closure can supply it (it factors through the spectrum → invariant above), and no
  field-of-values closure is known to.
-/

namespace SpectralPhysics.OffOrigin

open SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta

/-- A pure-M2 deformation: a κ-family of visible spectra whose eigenvalue data is held fixed
(the directed/eigenvector geometry varies off-spectrum). That M2 deformations have this
spectrum-freezing property is the modelling input (*Part: Off-Origin*; confirmed numerically in
`output/closure_probe.md`, where the joint heat trace is constant in κ). -/
structure M2Deformation where
  spec : ℝ → VisibleSpectrum
  frozen : ∀ κ κ', spec κ = spec κ'

/-- **Blindness of the closure (provable core).** Any spectral functional — anything that
factors through the visible spectrum — is constant along a pure-M2 deformation. So no spectral
closure (heat trace, SCSE `Γ(ζ_D)=ζ_D`, SAGF) has a gradient on the M2 axis. -/
theorem spectral_functional_M2_invariant
    (F : VisibleSpectrum → ℝ) (D : M2Deformation) (κ κ' : ℝ) :
    F (D.spec κ) = F (D.spec κ') := by
  rw [D.frozen κ κ']

/-- Corollary for the framework's even (M1) deficit: it cannot move along the directed axis. -/
theorem informationContent_M2_invariant (D : M2Deformation) (κ κ' : ℝ) :
    informationContent (D.spec κ) = informationContent (D.spec κ') :=
  spectral_functional_M2_invariant informationContent D κ κ'

/-- A selector of `eta_dir`. **Non-spectral** = it distinguishes deformations that share a
(frozen) spectrum, i.e. is not determined by the eigenvalue data (necessary for any forward
origin, by the invariance above). -/
def NonSpectral (sel : M2Deformation → ℝ) : Prop :=
  ∃ D D' : M2Deformation, (∀ κ κ', D.spec κ = D'.spec κ') ∧ sel D ≠ sel D'

/-- **OPEN.** A forward, observable-free origin for `eta_dir`: a non-spectral selector exists.
(The full statement adds framework-distinguishedness + uniqueness; even this weaker existence is
not established — Phases 1–2 give only negative evidence.) -/
def ForwardOriginExists : Prop := ∃ sel : M2Deformation → ℝ, NonSpectral sel

theorem forward_origin : ForwardOriginExists := by
  sorry -- OPEN: independence branch (Phase 1 BACK-SOLVE, Phase 2 FREE).

end SpectralPhysics.OffOrigin
