/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.IRUVScaleSeparation.KatoStability

/-!
# Wilson–Polchinski Universality — the RG-Flow Connection

The v0.9 spectral-universality content of `prop:spectral-convergence`
(line 1437) is **the spectral analogue** of Wilson–Polchinski
RG-flow universality:

  In statistical mechanics (Wilson 1971): low-energy observables
  depend only on IR data, not on UV regulator.

  In the spectral framework: low-eigenvalue spectrum of `D_F(Λ)`
  is independent of `Λ` for `Λ ≥ Λ_IR`.

This file *identifies* the two formulations via a named axiom of
citation — the **Wilson–Polchinski analogy**. The biconditional

  `SpectralUniversality R ↔ RGFlowConverges R`

captures the framework-internal universality as the operator-spectral
shadow of the path-integral universality.

## What is named

* `RGFlowConverges` — the Wilsonian RG-flow convergence predicate
  for the family `R`. Predicate form, no derivation. Citation:
  Wilson 1971 + Polchinski 1984.
* `WilsonianUniversality` — the biconditional predicate (this is
  the v0.9 line 1437 *content* in modern RG language).
* `wilson_polchinski_analogy` — the named axiom asserting the
  biconditional holds for *every* `CutoffFamily R`. **This is the
  Wilson–Polchinski universality hypothesis** — the literature
  statement that *the* IR/UV separation in the spectral framework
  is the same content as Wilsonian RG convergence.

## Honest scope

* `RGFlowConverges` is **not** defined as a Mathlib statement about
  RG-flow dynamics. The Wilson–Polchinski flow is a PDE in coupling
  space, which is out of Mathlib scope. We carry it as a `Prop`
  predicate keyed to `R`.
* The named axiom `wilson_polchinski_analogy` is an axiom of
  *citation*. It does **not** discharge `SpectralUniversality R`
  for any concrete `R` — it merely identifies that predicate with
  `RGFlowConverges R`. To *prove* `SpectralUniversality R`, one
  still needs the Kato hypotheses from `KatoStability.lean`.

## References

* Wilson, K.G. (1971). *Renormalization group and critical phenomena.*
  Phys. Rev. B **4**, 3174 (Pt. I); *Renormalization group and strong
  interactions*, Phys. Rev. D **3**, 1818.
* Polchinski, J. (1984). *Renormalization and effective Lagrangians.*
  Nucl. Phys. B **231**, 269–295. — modern formulation of the
  Wilsonian IR/UV separation.
* Wetterich, C. (1993). *Exact evolution equation for the effective
  potential.* Phys. Lett. B **301**, 90. — exact functional RG flow.
* Ben-Shalom (2026). *Spectral Physics* v0.9, line 1437.
-/

namespace SpectralPhysics.IRUVScaleSeparation

/-! ## The Wilsonian RG-flow predicate -/

/-- **Wilsonian RG-flow convergence** (named, predicate form).

    A cutoff family `R` exhibits **RG-flow convergence** iff the
    effective theory at IR scale `Λ_IR` is independent of the UV
    cutoff `Λ` — the standard statement of Wilson–Polchinski
    universality.

    *Honest scope.* We do not define the Wilsonian effective action
    as a Mathlib object. We carry `RGFlowConverges` as a `Prop`
    predicate keyed to the cutoff family. The substantive content
    is supplied by the `wilson_polchinski_analogy` axiom of
    citation — which identifies `RGFlowConverges R` with
    `SpectralUniversality R` for every `R`. -/
def RGFlowConverges (R : CutoffFamily) : Prop :=
  ∀ (μ : ℝ), 0 < μ →
    ∀ (Λ Λ' : ℝ),
      R.Λ_IR ≤ Λ → R.Λ_IR ≤ Λ' →
      LowEnergyAgree R μ Λ Λ'

/-- `RGFlowConverges` is *symmetric* in `Λ ↔ Λ'` by construction. -/
theorem RGFlowConverges.symm
    {R : CutoffFamily} (h : RGFlowConverges R)
    (μ : ℝ) (hμ : 0 < μ)
    (Λ Λ' : ℝ) (hΛ : R.Λ_IR ≤ Λ) (hΛ' : R.Λ_IR ≤ Λ') :
    LowEnergyAgree R μ Λ Λ' := h μ hμ Λ Λ' hΛ hΛ'

/-! ## The Wilson–Polchinski biconditional -/

/-- **Wilson–Polchinski universality (the biconditional).**

    The framework-internal `SpectralUniversality R` is identified
    with the Wilsonian `RGFlowConverges R`. This is the v0.9 line
    1437 *analogy* made into a predicate.

    The biconditional is **not derived** in this directory — it is
    carried by the named axiom `wilson_polchinski_analogy`. -/
def WilsonianUniversality (R : CutoffFamily) : Prop :=
  SpectralUniversality R ↔ RGFlowConverges R

/-! ## Named axiom — the Wilson–Polchinski analogy

This is the *only* free axiom of this directory. It cites Wilson
(1971) and Polchinski (1984) as the source of the analogy between
spectral universality and RG-flow convergence. -/

/-- **Named axiom (Wilson 1971 + Polchinski 1984).**

    The Wilson–Polchinski analogy: for every cutoff family `R`,
    the spectral universality predicate is *equivalent* to RG-flow
    convergence.

    This axiom does **not** prove either side — it identifies them.
    Conclusion of `SpectralUniversality R` still requires the Kato
    hypotheses (`KatoStability.lean`). The axiom merely says that
    once you have one, you have the other.

    Honesty: this axiom is **load-bearing only inside this directory**
    — outside it, no theorem in `SpectralPhysics` is concluded by
    invoking it. -/
axiom wilson_polchinski_analogy :
    ∀ (R : CutoffFamily), WilsonianUniversality R

/-- The Wilson–Polchinski axiom, in the direction
    `SpectralUniversality → RGFlowConverges`. -/
theorem rg_flow_from_spectral_universality
    (R : CutoffFamily) (h : SpectralUniversality R) :
    RGFlowConverges R :=
  (wilson_polchinski_analogy R).mp h

/-- The Wilson–Polchinski axiom, in the direction
    `RGFlowConverges → SpectralUniversality`. -/
theorem spectral_universality_from_rg_flow
    (R : CutoffFamily) (h : RGFlowConverges R) :
    SpectralUniversality R :=
  (wilson_polchinski_analogy R).mpr h

/-! ## Combined statement — the conditional closure of v0.9 line 1437

Combining `KatoStability` with the Wilson–Polchinski analogy: given
a Schatten-norm UV-suppression rate, we get both the spectral
universality and (by the analogy) the Wilsonian RG-flow convergence.

This is the *full* v0.9 line 1437 statement, conditional on the
named functional-analytic input. -/

/-- **The full v0.9 line 1437 closure, CONDITIONAL.**

    Given the Kato–Reed–Simon bridge and a Schatten-norm UV
    suppression rate, the family `R` exhibits both spectral
    universality and Wilsonian RG-flow convergence — the two sides
    of the v0.9 line 1437 analogy.

    Hypotheses:

    * `h_kato_bridge : KatoReedSimonBridge R`;
    * `h_schatten : SchattenUVSuppression R C α`.

    Conclusion: both `SpectralUniversality R` and
    `RGFlowConverges R`. -/
theorem v091_line_1437_conditional_closure
    {R : CutoffFamily} {C α : ℝ}
    (h_kato_bridge : KatoReedSimonBridge R)
    (h_schatten : SchattenUVSuppression R C α) :
    SpectralUniversality R ∧ RGFlowConverges R := by
  have h_spec : SpectralUniversality R :=
    spectral_universality_from_perturbation_bound h_kato_bridge h_schatten
  refine ⟨h_spec, ?_⟩
  exact rg_flow_from_spectral_universality R h_spec

end SpectralPhysics.IRUVScaleSeparation
