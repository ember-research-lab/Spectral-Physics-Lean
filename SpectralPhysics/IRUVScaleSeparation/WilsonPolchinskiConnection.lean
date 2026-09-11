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
* `wilson_polchinski_analogy` — **SHELL** (2026-08-18 content audit,
  U6). Declared as a named axiom of citation asserting the
  biconditional for every `CutoffFamily R`, but it is provable outright
  from the two definitions in this file (`Vacuity.lean:wp_provable`,
  kernel axioms only). It assumes nothing about Wilsonian RG flow and
  must not be cited as importing literature content.

## Decl classes (2026-08-18 content audit)

* `RGFlowConverges`, `WilsonianUniversality` — DEFINITIONAL predicates.
* `RGFlowConverges.symm` — SHELL: returns its own hypothesis applied.
* `wilson_polchinski_analogy` — **SHELL** (provable outright; see above).
* `rg_flow_from_spectral_universality`,
  `spectral_universality_from_rg_flow` — SHELL: `.mp`/`.mpr` of the
  shell axiom.
* `v091_line_1437_conditional_closure` — its second conjunct is SHELL
  (it comes from the shell axiom); only the `SpectralUniversality`
  conjunct carries the Kato/Schatten hypotheses. It is **not** a
  closure of v0.9 line 1437.

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

/-- **PROVABLE — was an axiom until 2026-09-10 (soundness census, CITE-PROVABLE).**
    Provable because `WilsonianUniversality` follows from the `CutoffFamily`
    fields; there is no RG content. This does NOT formalize Wilson–Polchinski
    universality; do not cite it as such.

    **SHELL**: provable outright from the two predicate definitions; it
    carries no Wilson–Polchinski content and must not be cited as a
    closure.

    The 2026-08-18 content audit (U6) showed that
    `∀ R, WilsonianUniversality R` is a theorem of this file's own
    definitions — see `lean-content-audit-2026-08-18/Vacuity.lean`,
    where `wp_provable` discharges it with kernel axioms only (forward:
    `SpectralUniversality.symmetric`; backward: `le_trans` on the two
    cutoffs).  Naming it after Wilson (1971) and Polchinski (1984) is
    laundering-by-citation: nothing about RG flow is being assumed or
    used, because `RGFlowConverges` is a `Prop` shadow of
    `SpectralUniversality` rather than an independent statement about
    the Wilsonian effective action.

    Kept as an `axiom` rather than demoted to a theorem because the
    proof, while short, is not mechanical (`rfl`/`norm_num`/`decide`);
    demoting it is a semantic change and out of scope for this
    labels-only pass.  If it is demoted later, the two predicates need
    to be genuinely independent first, or the demotion just makes the
    vacuity visible without fixing it.

    Statement as written: for every cutoff family `R`, the spectral
    universality predicate is equivalent to RG-flow convergence. -/
theorem wilson_polchinski_analogy :
    ∀ (R : CutoffFamily), WilsonianUniversality R := by
  intro R
  constructor
  · intro h μ hμ Λ Λ' hΛ hΛ'; exact h.symmetric μ hμ Λ Λ' hΛ hΛ'
  · intro h μ hμ Λ Λ' hΛ hΛΛ'; exact h μ hμ Λ Λ' hΛ (le_trans hΛ hΛΛ')

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

/-! ## Combined statement — NOT a closure of v0.9 line 1437

Combining `KatoStability` with the Wilson–Polchinski analogy: given
a Schatten-norm UV-suppression rate, we get the spectral universality
and (by the shell axiom) the Wilsonian RG-flow convergence.

Because `wilson_polchinski_analogy` is SHELL (provable outright from
the definitions in this file), the second conjunct adds nothing: it is
`SpectralUniversality` re-read through a `Prop` alias, not a statement
about the Wilsonian effective action. Do not cite this as closing
v0.9 line 1437. -/

/-- Conditional statement combining the Kato input with the SHELL
    Wilson–Polchinski alias. **Not a closure of v0.9 line 1437.**

    Given the Kato–Reed–Simon bridge and a Schatten-norm UV
    suppression rate, the family `R` exhibits spectral universality;
    the `RGFlowConverges` conjunct then follows from the SHELL axiom
    `wilson_polchinski_analogy` and carries no independent content.

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
