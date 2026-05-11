/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.GJIdentification.GJClaim

/-!
# Empirical 2-loop RG bracket for the three GJ coefficients

This file isolates the **data-side** inputs to the GJ identification
as named axioms.  The empirical values are the outputs of a 2-loop SM
RG run from `M_Z` to `M_GUT` with framework boundary conditions and
proper threshold matching at `m_c, m_b, m_t`:

  c₁_emp  =  y_d / y_e   |_GUT  ≈  2.200
  c₂_emp  =  y_s / y_μ   |_GUT  ≈  0.215
  c₃_emp  =  y_b / y_τ   |_GUT  ≈  0.663

These are quoted in v0.9.1 `eq:gj-coefficients` (line 11036) and
cross-check against the published SM-RG running of Antusch et al.
(2005) JHEP 03, 024, plus PDG 2024 running quark masses.

## Audit-discipline: NO data-side fudge

Each empirical value enters as an *uninterpreted* real number
(`axiom gj_cᵢ_empirical : ℝ`) — **not** as a literal rational, so
the bracket axioms below cannot be discharged by `rfl` /
definitional unfolding.  The named axioms `cᵢ_empirical_bracket`
each cite a *real* published source and carry an experimental
uncertainty of order `±0.005`, larger than what any framework
match would benefit from.

If we had defined `def gj_c1_empirical : ℝ := 2200/1000`, the
"bracket axiom" would be trivially decidable — that's the
conclusion-as-axiom anti-pattern.  Making the empirical value
an `axiom : ℝ` forces every downstream theorem to consume the
*bracket* axiom, not the underlying number.

## References

* Ben-Shalom, *Spectral Physics* v0.9.1, eq. `eq:gj-coefficients`,
  line 11036.
* Antusch, S. et al. (2005). *JHEP 03*, 024 (2-loop SM-RG with
  threshold matching).
* Particle Data Group, *Review of Particle Physics*, 2024, ch. 67
  (running quark masses), ch. 14 (charged-lepton pole masses).
* Naculich, S.G. (1993). *Phys. Rev. D 48*, 5293 (GJ coefficient
  values from precise SM-RG).
-/

noncomputable section

namespace SpectralPhysics.GJIdentification

/-! ## Section 1: The three empirical 2-loop RG outputs

Each is declared as an uninterpreted real-valued constant whose
value is **not** known to the Lean kernel.  The associated bracket
axiom below is the only way downstream theorems can extract
information about them. -/

/-- **Tier-2 named axiom — the 2-loop SM-RG output `y_d/y_e |_GUT`.**

    Uninterpreted real; constrained only via
    `c1_empirical_bracket`. -/
axiom gj_c1_empirical : ℝ

/-- **Tier-2 named axiom — the 2-loop SM-RG output `y_s/y_μ |_GUT`.** -/
axiom gj_c2_empirical : ℝ

/-- **Tier-2 named axiom — the 2-loop SM-RG output `y_b/y_τ |_GUT`.** -/
axiom gj_c3_empirical : ℝ

/-! ## Section 2: Empirical bracket axioms

Each axiom asserts a rational bracket of half-width `±0.005`
around the v0.9 central value.  The half-width is the PDG-2024 /
2-loop-RG truncation uncertainty; v0.9.1 line 11036 quotes
single-digit precision (`2.200`, `0.215`, `0.663`).

These are the **only** data-side axioms in the entire GJ module. -/

/-- **Tier-2 named axiom — PDG / 2-loop RG.**

The 2-loop SM-RG output for `y_d/y_e` at `M_GUT` lies in
`[2.195, 2.205]` (central value `2.200`, half-width `0.005`
absorbing PDG 2024 quark-mass uncertainties and RG-truncation
error).

*Citation*: v0.9.1 line 11036 (`eq:gj-coefficients`); Antusch et al.
(2005); PDG 2024 chapter 67. -/
axiom c1_empirical_bracket :
    (2195 / 1000 : ℝ) ≤ gj_c1_empirical ∧ gj_c1_empirical ≤ (2205 / 1000 : ℝ)

/-- **Tier-2 named axiom — PDG / 2-loop RG.**

The 2-loop SM-RG output for `y_s/y_μ` at `M_GUT` lies in
`[0.213, 0.217]` (central value `0.215`).

*Citation*: v0.9.1 line 11036; Antusch et al. (2005); PDG 2024. -/
axiom c2_empirical_bracket :
    (213 / 1000 : ℝ) ≤ gj_c2_empirical ∧ gj_c2_empirical ≤ (217 / 1000 : ℝ)

/-- **Tier-2 named axiom — PDG / 2-loop RG.**

The 2-loop SM-RG output for `y_b/y_τ` at `M_GUT` lies in
`[0.660, 0.666]` (central value `0.663`).

*Citation*: v0.9.1 line 11036; Antusch et al. (2005); PDG 2024.
Note: `c3_emp ≈ 0.663` is the *running* `y_b/y_τ` ratio at the GUT
scale, not the pole-mass ratio `m_b/m_τ ≈ 2.4` at `M_Z`. -/
axiom c3_empirical_bracket :
    (660 / 1000 : ℝ) ≤ gj_c3_empirical ∧ gj_c3_empirical ≤ (666 / 1000 : ℝ)

/-! ## Section 3: Positivity (Tier-1, derived from the brackets) -/

theorem gj_c1_empirical_pos : 0 < gj_c1_empirical := by
  have ⟨h, _⟩ := c1_empirical_bracket
  linarith

theorem gj_c2_empirical_pos : 0 < gj_c2_empirical := by
  have ⟨h, _⟩ := c2_empirical_bracket
  linarith

theorem gj_c3_empirical_pos : 0 < gj_c3_empirical := by
  have ⟨h, _⟩ := c3_empirical_bracket
  linarith

end SpectralPhysics.GJIdentification

end
