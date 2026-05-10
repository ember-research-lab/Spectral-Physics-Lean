/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.MajoranaSelfRef.JSelfConjugate
import SpectralPhysics.MajoranaSelfRef.TriadicPartition
import SpectralPhysics.MajoranaSelfRef.SelfReferenceClosure

/-!
# Verdict: Does Self-Reference Machinery Determine y_R?

## The hypothesis under test

The user's load-bearing follow-up after the negative
`compute/majorana-block-residue` result:

> Majorana fermions are J-self-conjugate.  Since the framework's
> foundation is self-reference, perhaps `y_R` lives in the
> self-reference machinery, not in standard see-saw NCG geometry.

## What this branch establishes (Tier 1)

1. **Structural locus** (`JSelfConjugate.lean`): `(1,1)_0` is the
   unique J-self-conjugate sub-rep of SO(10) `16`.
2. **Triadic 1:2 partition is order-1** (`TriadicPartition.lean`):
   `(1/2)^n` for `n ≤ 10` does not reach y_R.  **Negative for direct
   1:2 reading.**
3. **τ-power and additive coincidences** (`SelfReferenceClosure.lean`):
   τ^8 ≈ y_R within factor 2; `9+φ ≈ −ln(y_R)` within `1/3`.

## The verdict

### **PARTIAL.**

* Self-reference machinery uniquely **identifies** the locus of `y_R`.
* Self-reference machinery **constrains** y_R to the τ^8 (≈ 7+δ) window.
* Self-reference machinery does **NOT** uniquely *determine* y_R,
  because the exponent (8 in Probe 2, 7+δ in Probe 3) is not
  derivable from primitives at this stage.

### What's needed to upgrade PARTIAL → YES

A **structural derivation of the exponent**:

* **Atiyah–Singer index** for the J-self-conjugate sector.
* **η-invariant** of the spectral triple restricted to (1,1)_0.
* **Zeta-determinant decomposition** giving exponent 8 as a count.
* **Self-Model Deficit refinement** to a single eigenvalue equation.

None is in v0.9 or this branch.

## Honest dual reading

The fact that **four** different structural primitives give close
fits within factor 2 of y_R is **suspicious** — it suggests the
bracket `[2 × 10⁻⁵, 6 × 10⁻⁵]` is wide enough that any exponential
of a primitive number will fall in it for some nearby integer
exponent.

Discriminating between
* (i) "the framework's primitives WANT to land near y_R" and
* (ii) "the bracket is wide enough that any fit succeeds"

is the substantive research question flagged for follow-up.

## References

* `compute/majorana-block-residue/STATUS.md` (the prior branch).
* `pre_geometric/y_r_chirality_unification/survey.md` §6.
* `pre_geometric/baker_selects_yR/verdict.md`.
* `pre_geometric/ko_dim6_inputs/verdict.md`.
-/

namespace SpectralPhysics.MajoranaSelfRef.Verdict

open SpectralPhysics.MajoranaSelfRef
open SpectralPhysics.MajoranaSelfRef.SelfReferenceClosure

/-! ## Tier-1 verdict theorems -/

/-- **Tier 1.**  ν_R is J-self-conjugate. -/
theorem yR_locus_is_J_self_conjugate :
    GaugeRep.isJSelfConjugate repNu_R :=
  repNu_R_is_JSelfConj

/-- **Tier 1.**  The five other sub-reps are NOT J-self-conjugate. -/
theorem yR_locus_unique :
    ¬ GaugeRep.isJSelfConjugate repQ_L ∧
    ¬ GaugeRep.isJSelfConjugate repU_Rc ∧
    ¬ GaugeRep.isJSelfConjugate repD_Rc ∧
    ¬ GaugeRep.isJSelfConjugate repL_L ∧
    ¬ GaugeRep.isJSelfConjugate repE_Rc :=
  ⟨repQ_L_not_JSelfConj, repU_Rc_not_JSelfConj, repD_Rc_not_JSelfConj,
   repL_L_not_JSelfConj, repE_Rc_not_JSelfConj⟩

/-- **Tier 1.**  The Fiedler 1:2 ratio is `~10⁴ ×` larger than y_R. -/
theorem fiedler_does_not_pin_yR :
    SpectralPhysics.MajoranaSelfRef.TriadicPartition.fiedler_min_max_ratio >
    10000 * SpectralPhysics.MajoranaSelfRef.TriadicPartition.y_R_target :=
  SpectralPhysics.MajoranaSelfRef.TriadicPartition.fiedler_min_max_ratio_far_from_y_R

/-- **Tier 1.**  τ^8 brackets y_R within factor 2. -/
theorem tau_pow_8_coincidence :
    tau_pow_8 < 2 * y_R_target ∧ y_R_target < 2 * tau_pow_8 :=
  tau_pow_8_close_to_y_R

/-- **Tier 1.**  `S_struct = 9 + φ` matches `−ln(y_R)` within `1/3`. -/
theorem S_struct_coincidence :
    |S_struct - neg_log_y_R_target| < 1 / 3 :=
  S_struct_close_to_target

/-- **Tier 1.**  τ^7 too large by factor 3; τ^9 too small by factor 3.
    Only τ^8 brackets. -/
theorem tau_exponent_uniquely_brackets :
    tau_pow_7 > 3 * y_R_target ∧ tau_pow_9 < y_R_target / 3 :=
  ⟨tau_pow_7_too_large, tau_pow_9_too_small⟩

/-- **The structural verdict (Tier 1).**

    Self-reference machinery:
    * **identifies** the y_R locus (J-self-conjugate sector),
    * **constrains** y_R magnitudinally (τ^8 within factor 2),
    * **does not derive** the exponent uniquely.

    The verdict on the user's hypothesis is **PARTIAL**. -/
theorem structural_verdict :
    GaugeRep.isJSelfConjugate repNu_R ∧
    (tau_pow_8 < 2 * y_R_target ∧ y_R_target < 2 * tau_pow_8) ∧
    (tau_pow_7 > 3 * y_R_target ∧ tau_pow_9 < y_R_target / 3) := by
  refine ⟨yR_locus_is_J_self_conjugate, tau_pow_8_coincidence,
          tau_exponent_uniquely_brackets⟩

/-! ## What this verdict explicitly does NOT prove

The conjectural identification `y_R = τ^8` is recorded as
`SelfReferenceClosure.y_R_self_reference_conjecture` (Tier-3
axiom).  We do NOT use it in any Tier-1 result here.  The
structural verdict above is fully derived from Tier-1 numerics
on `τ`, `φ`, and `y_R_target`. -/

end SpectralPhysics.MajoranaSelfRef.Verdict
