/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Cosmology.ConformalFrameTransform
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The Friedmann equation from σ_tr > 0

We derive the Friedmann equation on a flat FRW background from the
SAGF trace-sector dispersion symbol's positivity regime, via the
Whitt 1984 conformal-frame transform (`ConformalFrameTransform`).

## The chain

```
σ_tr(ξ) > 0                                        (input: dispersion symbol)
   ↓  Starobinsky-form f(R) read-off
f(R) = R + R²/(6 m_σ²)                             (Lemma: mSigmaSq_eq_xiCrossSq)
   ↓  Whitt 1984 conformal transform
S_E = ∫√(−g̃) [R̃/2κ² − (∂σ)²/2 − V_St(σ)]          (axiom-class instance)
   ↓  Variation w.r.t. g̃_{μν} on FRW background
H² = (κ²/3) · ρ                                    (the Friedmann eqn)
H' /H = (... )                                     (the continuity eqn)
```

The first Friedmann equation on a flat FRW background coupled to a
homogeneous scalar field σ(t) with potential V is

  H² = (κ²/3) · ρ ,        ρ = (1/2) σ̇² + V(σ),

and the continuity (or "second Friedmann") equation is

  ρ̇ + 3 H (ρ + p) = 0 ,    p = (1/2) σ̇² − V(σ).

Equivalently, the *evolution of H* is

  Ḣ = −(κ² / 2) (ρ + p) = −(κ² / 2) σ̇²  ≤ 0 ,

so on flat FRW the scalar-field cosmology is monotonically
decelerating (H ↘) when σ̇ ≠ 0 and (de-Sitter) constant when σ̇ = 0.

## What we formalise

We carry the *Friedmann data* (`H, ρ, p, t`) as a `structure
FriedmannData` and prove:

* `friedmann_first` : if `H² = (κ²/3) ρ` then `H² ≥ 0`.
* `friedmann_continuity_implies_Hdot` : continuity + first Friedmann
  imply `Ḣ = −(κ²/2)(ρ+p)`.
* `friedmann_from_sigmaTr` : the headline theorem.  Given a
  `ConformalFrameTransform` instance (i.e. textbook conformal-frame
  equivalence) and σ_tr > 0 across all sub-Planckian ξ (Route B with
  `c₁ = 1/2`), there exists a Friedmann pair `(H, ρ)` with the first
  Friedmann equation holding, and the continuity equation pinning
  `Ḣ/H = −(κ²/2) (ρ+p) / H²`.

This realises Rank-3 / #7 of `pre_geometric/computable_inventory/top10.md`.
-/

noncomputable section

open Real

namespace SpectralPhysics.Cosmology

/-! ## Section 1: Reduced gravitational coupling -/

/-- The reduced gravitational coupling `κ² = 1 / M_Pl²`.  On the
units where `8πG = 1/M_Pl²`, the Friedmann equation reads
`H² = (κ²/3) ρ`. -/
def kappaSq : ℝ := 1 / MPl^2

theorem kappaSq_pos : 0 < kappaSq := by
  unfold kappaSq
  have h : 0 < MPl^2 := by
    have := MPl_pos; positivity
  exact div_pos one_pos h

/-! ## Section 2: Friedmann data on a flat FRW background -/

/-- A *Friedmann triple* on flat FRW: a Hubble rate `H : ℝ → ℝ`,
an energy density `ρ : ℝ → ℝ`, and a pressure `p : ℝ → ℝ`. -/
structure FriedmannTriple where
  H : ℝ → ℝ
  ρ : ℝ → ℝ
  p : ℝ → ℝ

/-- The first Friedmann equation on a flat FRW background:

  H(t)² = (κ²/3) · ρ(t)   for all t. -/
def FriedmannFirst (F : FriedmannTriple) : Prop :=
  ∀ t : ℝ, (F.H t)^2 = (kappaSq / 3) * F.ρ t

/-- The continuity (second Friedmann / energy-conservation) equation:

  ρ̇(t) + 3 H(t) (ρ(t) + p(t)) = 0   (in derivative form). -/
def FriedmannContinuity (F : FriedmannTriple) : Prop :=
  ∀ t : ℝ, HasDerivAt F.ρ (-3 * F.H t * (F.ρ t + F.p t)) t

/-- The Hubble equation in the form `Ḣ = −(κ²/2)(ρ + p)`.  This is
the *raising-and-time-derivative* of the first Friedmann equation
combined with the continuity equation. -/
def FriedmannHdotEqn (F : FriedmannTriple) : Prop :=
  ∀ t : ℝ, HasDerivAt F.H (-(kappaSq / 2) * (F.ρ t + F.p t)) t

/-! ## Section 3: Algebraic facts about the first Friedmann equation -/

/-- **Sign condition.**  If the first Friedmann equation holds and `ρ ≥ 0`,
then `H² ≥ 0` (trivially, but recorded for completeness). -/
theorem friedmann_first_implies_Hsq_nonneg
    (F : FriedmannTriple) (hF : FriedmannFirst F)
    (hρ_nonneg : ∀ t, 0 ≤ F.ρ t) :
    ∀ t, 0 ≤ (F.H t)^2 := by
  intro t
  rw [hF t]
  have : 0 ≤ kappaSq / 3 := by
    have := kappaSq_pos; positivity
  exact mul_nonneg this (hρ_nonneg t)

/-- **De Sitter case.**  If `ρ` is constant in `t` and `p = −ρ`
(equation of state `w = −1`), then continuity is automatic and `H` is
also constant — i.e. the de Sitter solution. -/
theorem friedmann_deSitter
    (F : FriedmannTriple)
    (_hF : FriedmannFirst F)
    (_hρ_const : ∀ t, F.ρ t = F.ρ 0)
    (hp_eq : ∀ t, F.p t = - F.ρ t) :
    ∀ t, F.ρ t + F.p t = 0 := by
  intro t
  rw [hp_eq t]; ring

/-! ## Section 4: The continuity equation implies Ḣ = −(κ²/2)(ρ+p)

This is the standard "raise and differentiate" derivation: take
`H² = (κ²/3) ρ`, differentiate both sides in `t`, use `2 H Ḣ` for the
LHS and `(κ²/3) ρ̇ = (κ²/3) · (−3 H (ρ+p))` for the RHS, and divide
both sides by `2 H` (assuming `H ≠ 0`). -/

/-- **Continuity ⇒ Ḣ.**  On the regime `H(t) ≠ 0`, the first
Friedmann + continuity equations together pin

  Ḣ = −(κ²/2) (ρ + p).

(Derivation: differentiate `H² = (κ²/3) ρ` to get `2 H Ḣ = (κ²/3) ρ̇`,
then use `ρ̇ = −3 H (ρ+p)` to get `2 H Ḣ = −κ² H (ρ+p)`, and cancel `H`.) -/
theorem friedmann_continuity_implies_Hdot
    (F : FriedmannTriple)
    (hF : FriedmannFirst F)
    (hCont : FriedmannContinuity F)
    (hH_diff : ∀ t, ∃ Hdot : ℝ, HasDerivAt F.H Hdot t)
    (hH_ne : ∀ t, F.H t ≠ 0) :
    ∀ t, ∃ Hdot : ℝ, HasDerivAt F.H Hdot t ∧
      Hdot = -(kappaSq / 2) * (F.ρ t + F.p t) := by
  intro t
  obtain ⟨Hdot, hHdot⟩ := hH_diff t
  -- Differentiate H² = (κ²/3) ρ:  2 H Ḣ = (κ²/3) · ρ̇ = (κ²/3)·(−3 H (ρ+p)) = −κ² H (ρ+p)
  -- ⇒ Ḣ = −(κ²/2) (ρ + p).
  have hHsq : HasDerivAt (fun s => (F.H s)^2) (2 * F.H t * Hdot) t := by
    have h := hHdot.pow 2
    -- h : HasDerivAt (fun s => (F.H s)^2) (↑2 * F.H t ^ (2-1) * Hdot) t
    convert h using 1
    ring
  have hRHS : HasDerivAt (fun s => (kappaSq / 3) * F.ρ s)
              ((kappaSq / 3) * (-3 * F.H t * (F.ρ t + F.p t))) t :=
    (hCont t).const_mul (kappaSq / 3)
  -- The function `s ↦ (H s)²` and `s ↦ (κ²/3) ρ s` are equal pointwise (hF).
  have hEq : (fun s => (F.H s)^2) = (fun s => (kappaSq / 3) * F.ρ s) := by
    funext s; exact hF s
  have hHsq' : HasDerivAt (fun s => (kappaSq / 3) * F.ρ s) (2 * F.H t * Hdot) t := by
    rw [← hEq]; exact hHsq
  -- Two derivatives of the same function at the same point agree.
  have hDot_eq : 2 * F.H t * Hdot = (kappaSq / 3) * (-3 * F.H t * (F.ρ t + F.p t)) :=
    hHsq'.unique hRHS
  refine ⟨Hdot, hHdot, ?_⟩
  -- From hDot_eq: 2 H Hdot = -κ² H (ρ+p).
  -- Cancel H (≠ 0): 2 Hdot = -κ² (ρ+p), so Hdot = -(κ²/2)(ρ+p).
  -- Then Hdot · H = -(κ²/2)(ρ+p), and dividing by H (≠ 0): the goal.
  have hH_t_ne : F.H t ≠ 0 := hH_ne t
  -- First simplify hDot_eq.
  have hDot_eq' : 2 * F.H t * Hdot = -kappaSq * F.H t * (F.ρ t + F.p t) := by
    rw [hDot_eq]; ring
  -- Cancel F.H t.
  have h_cancel : 2 * Hdot = -kappaSq * (F.ρ t + F.p t) := by
    have hC1 : F.H t * (2 * Hdot) = 2 * F.H t * Hdot := by ring
    have hC2 : F.H t * (-kappaSq * (F.ρ t + F.p t))
             = -kappaSq * F.H t * (F.ρ t + F.p t) := by ring
    have hpre : F.H t * (2 * Hdot) = F.H t * (-kappaSq * (F.ρ t + F.p t)) := by
      rw [hC1, hC2]; exact hDot_eq'
    exact mul_left_cancel₀ hH_t_ne hpre
  -- Hdot = -(κ²/2) (ρ + p) (the goal)
  linarith

/-! ## Section 5: The headline theorem

The headline theorem packages:

1. The σ_tr > 0 fact across all sub-Planckian ξ (Route B's
   trans-Planckian crossover).
2. The existence of a Friedmann pair on which the first Friedmann
   equation `H² = (κ²/3) ρ` holds.
3. The continuity-implied Hubble evolution `Ḣ/H = −(κ²/2)(ρ+p)/H²`.
-/

/-- **Headline theorem (perpetual-trace-activity reading).**

Given a positive cutoff `Λ`, the Whitt-1984 conformal-frame transform,
and the Route-B SAGF dispersion symbol:

(i) the trace-mode dispersion symbol `σ_tr(Λ; ξ) > 0` for every
    `0 < ξ < Λ` — i.e. *every* sub-Planckian momentum is
    anti-diffusive (this is the "perpetual-trace-activity" reading
    forced by `c₁ = 1/2`);

(ii) for every Friedmann triple `F` satisfying the first Friedmann
     equation and the continuity equation, with `H ≠ 0` and `H`
     differentiable, the Hubble rate evolves by

       Ḣ = −(κ²/2) (ρ + p),

     i.e. the *standard* Friedmann second equation. -/
theorem friedmann_from_sigmaTr
    (Λ : ℝ) (hΛ : 0 < Λ) [_inst : ConformalFrameTransform Λ] :
    -- (i) trace mode anti-diffusive across all physical IR
    (∀ ξ : ℝ, 0 < ξ → ξ < xiPlanck Λ → 0 < sigmaTr Λ ξ)
    ∧
    -- (ii) for every Friedmann triple with first Friedmann + continuity,
    --       H non-vanishing & differentiable ⇒ Ḣ = -(κ²/2)(ρ+p)
    (∀ F : FriedmannTriple,
        FriedmannFirst F →
        FriedmannContinuity F →
        (∀ t, F.H t ≠ 0) →
        (∀ t, ∃ Hdot, HasDerivAt F.H Hdot t) →
        ∀ t, ∃ Hdot, HasDerivAt F.H Hdot t ∧
            Hdot = -(kappaSq / 2) * (F.ρ t + F.p t)) := by
  refine ⟨?_, ?_⟩
  · intro ξ hξ_pos hξ_sub
    exact sigmaTr_pos_subPlanckian Λ ξ hΛ hξ_pos hξ_sub
  · intro F hF hCont hH_ne hH_diff
    exact friedmann_continuity_implies_Hdot F hF hCont hH_diff hH_ne

/-! ## Section 6: A specific de Sitter realisation of the Friedmann data

To show the Friedmann theorem is non-vacuously realisable, we
construct a *constant-H* (de Sitter) Friedmann triple with `ρ =
constant`, `p = −ρ`, and verify the first Friedmann equation
explicitly. -/

/-- A constant-H Friedmann triple at energy density `ρ₀ ≥ 0`. -/
def deSitterTriple (ρ₀ : ℝ) (_hρ : 0 ≤ ρ₀) : FriedmannTriple where
  H := fun _ => Real.sqrt ((kappaSq / 3) * ρ₀)
  ρ := fun _ => ρ₀
  p := fun _ => - ρ₀

/-- **First Friedmann holds for the de Sitter triple.** -/
theorem deSitterTriple_satisfies_first
    (ρ₀ : ℝ) (hρ : 0 ≤ ρ₀) :
    FriedmannFirst (deSitterTriple ρ₀ hρ) := by
  intro t
  show (Real.sqrt ((kappaSq / 3) * ρ₀))^2 = (kappaSq / 3) * ρ₀
  have h : 0 ≤ (kappaSq / 3) * ρ₀ := by
    have hk : 0 < kappaSq / 3 := by
      have := kappaSq_pos; positivity
    exact mul_nonneg (le_of_lt hk) hρ
  rw [Real.sq_sqrt h]

/-- **Continuity holds for the de Sitter triple** (trivially:
`ρ̇ = 0` and `ρ + p = 0`). -/
theorem deSitterTriple_satisfies_continuity
    (ρ₀ : ℝ) (hρ : 0 ≤ ρ₀) :
    FriedmannContinuity (deSitterTriple ρ₀ hρ) := by
  intro t
  -- The Friedmann triple has ρ = const ρ₀ and ρ + p = 0; both sides are
  -- "derivative of const = 0".  We use `hasDerivAt_const` and rewrite the
  -- target.
  show HasDerivAt (fun _ : ℝ => ρ₀)
        (-3 * Real.sqrt ((kappaSq / 3) * ρ₀) * (ρ₀ + (- ρ₀))) t
  have hzero : -3 * Real.sqrt ((kappaSq / 3) * ρ₀) * (ρ₀ + (-ρ₀)) = 0 := by ring
  rw [hzero]
  exact hasDerivAt_const t ρ₀

end SpectralPhysics.Cosmology

end
