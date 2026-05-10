/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.EtaJSelfConj.APSIndex

/-!
# Verdict: Does the η-Invariant + Spectral-Flow Combination Yield 8?

## The hypothesis under test

  *"η(D_F |_{(1,1)_0}) plus a non-trivial spectral-flow count yields
   the integer 8 (the residual exponent in `y_R = τ^8`)."*

## The verdict

### **DEGENERATE.**

Both summands of the proposed APS-style combination vanish identically
on the J-self-conjugate sub-block of `D_F`:

  - `η(D_F |_{(1,1)_0}) = 0`        — Majorana pairing
                                       (`EtaInvariant.lean`)
  - `sf({D_F^t}_{0 → physical}) = 0` — symmetric splitting
                                       (`SpectralFlow.lean`)

so the Bismut–Freed pairing `η + 2·sf = 0`, and the full APS index
gives either `0` (at `y_R = physical`) or `-Ngen/2 = -3/2` (at
`y_R = 0`).  Neither is 8.

### Why this route is *structurally* dead

The same KO-dim-6 sign triple `(J² = +1, JD = DJ, Jγ = -γJ;
Connes-Marcolli §15.4)` that

* picks `(1,1)_0 = ν_R` as the unique J-self-conjugate sub-rep of
  the SO(10) 16,
* underwrites the (A.1) bit of the framework's foundation,
* makes ν_R "Majorana-able",

ALSO forces:

* the η-invariant to vanish identically (term-by-term Majorana
  cancellation, no regularisation can rescue it),
* the spectral flow to be net-zero (each zero mode splits to ±M_R
  symmetrically, giving one up-crossing and one down-crossing per
  generation).

There is no information left in the (η, sf) pair from which the
integer 8 can be extracted — a structural impossibility.

### Difference from the AS-index branch verdict

| Branch                                 | Result    | Reason                              |
|----------------------------------------|-----------|-------------------------------------|
| `compute/atiyah-singer-J-self-conj`    | NO (= 0)  | Singlet bundle ⇒ AS index vanishes  |
| `compute/eta-invariant-J-self-conj`    | DEGENERATE| Majorana pairing ⇒ η ≡ 0, sf ≡ 0    |

Both vanish, but for different structural reasons:

* The AS-index vanishes because the bundle is a *singlet* under
  the SM gauge group (Lie-algebra generator acts as zero in `ch(E)`).
* The η-invariant + spectral-flow vanish because the spectrum is
  *J-self-conjugate-paired* (every λ comes with -λ).

These two reasons are independent: even if the bundle were not
singlet, J-self-conjugacy alone would still force η = 0 and sf = 0.

The AS branch's verdict was `NO` because `0 ≠ 8`.  This branch's
verdict is `DEGENERATE` because there's no hidden information in
the candidate quantities — the cancellation is *built into* the
J-self-conjugacy that motivated this sector in the first place.
A trivially-zero quantity cannot be promoted to a non-zero integer
by any choice of regularisation or boundary data.

## Consequence chain (negative)

The original hope:
  *"If η + sf = 8, then `y_R = τ^8` is structurally forced
   ⇒ OP3 unconditional, ζ_F'(0) unconditional, η_B Formula B
   becomes derivation."*

The actual result:
  η + sf ≡ 0 ⇒ `y_R = τ^8` is **NOT** structurally forced by APS.

Hence, in addition to the AS-index closure:

* **OP3** stays conditional on the see-saw IC `M_R = 5 × 10^14 GeV`.
* **ζ_F'(0)** retains its dependence on the y_R input.
* **η_B Formula B** remains a working hypothesis, not a derivation.
* **`y_R` is transcendent IC** alongside the (A.1) bit (now firmer:
  TWO independent index/asymmetry routes have failed to derive it).

## What stays open

The remaining attack vectors flagged by the AS-index branch:

2. **ζ-function regularised dimension** `ζ_F(0; ν_R) = ?`.  (Open;
   different attack vector — ζ on a single sub-block.)
3. **Self-Model-Deficit refinement.**  (Open.)

Of these, (2) is the natural next dispatch (`compute/zeta-F-nuR-
regularized` in the branch list).  Note that ζ-regularisation may
*also* be defeated by Majorana symmetry: for `ζ_F(s) = ∑ |λ|^{-s}`,
both `+λ` and `-λ` contribute equally with multiplicity 2, so
`ζ_F(0; ν_R) = 2 · ζ^{(half)}` — no sign asymmetry to exploit.
But this needs its own dispatch.

## Tier classification

* **Tier 1 (proved here)**: η ≡ 0, sf ≡ 0, APS pairing ≡ 0.
* **Tier 1 (proved here)**: each ≠ 8.
* **Tier 1 (proved here)**: full APS index in `{0, -3/2}`, also ≠ 8.
* **Tier 3 (named axioms)**:
   - APS 1975 (Atiyah-Patodi-Singer Part I, equation (4.3));
   - APS 1976 (Part II, Theorem (3.10));
   - Bismut-Freed 1986 (η-spectral-flow relation);
   - KO-dim-6 sign triple (Connes 1996, Connes-Marcolli §15.4).

## Cross-links

* `compute/atiyah-singer-J-self-conj`:
  - AS index = 0 (sister branch, same negative consequence).
* `compute/majorana-self-reference`:
  - τ^8 numerical bracket (`SelfReferenceClosure.lean`).
  - PARTIAL verdict (`Verdict.lean`).
* `compute/majorana-block-residue`:
  - Hypothesis B selected, see-saw IC `M_R` retained.
* `compute/zeta-F-nuR-regularized`:
  - Next dispatch on the y_R bottleneck.

## References

* Atiyah, M.F., Patodi, V.K., Singer, I.M. (1975, 1976).
  "Spectral asymmetry and Riemannian geometry I, II, III."
  Math. Proc. Cambridge Phil. Soc. **77, 78, 79**.
* Bismut, J.-F., Freed, D.S. (1986).
  "The analysis of elliptic families II."  CMP **107**, 103–163.
* Connes, A. (1996). "Gravity coupled with matter and the foundation
  of noncommutative geometry."  CMP **182**, 155–176.
* Connes, A., Marcolli, M. (2008). *Noncommutative Geometry, Quantum
  Fields and Motives*, AMS Coll. Pub. **55**, §15.4 (KO-dim 6),
  §17 (η-invariant in spectral action).
-/

namespace SpectralPhysics.EtaJSelfConj.Verdict

open SpectralPhysics.EtaJSelfConj
open SpectralPhysics.IndexJSelfConj

/-! ## Tier-1 verdict theorems -/

/-- **Tier 1.**  The η-invariant of the J-self-conjugate sub-block
    is identically 0 (every `Ngen`, every Majorana mass `MR > 0`). -/
theorem eta_is_identically_zero (Ngen : ℕ) (MR : ℝ) (h : 0 < MR) :
    (nuR_spectrum Ngen MR h).etaInvariant = 0 :=
  nuR_etaInvariant_eq_zero Ngen MR h

/-- **Tier 1.**  The net spectral flow is identically 0. -/
theorem spectral_flow_is_identically_zero (Ngen : ℕ) (MR : ℝ) (h : 0 < MR) :
    totalNetFlow Ngen MR h = 0 :=
  totalNetFlow_eq_zero Ngen MR h

/-- **Tier 1.**  The Bismut–Freed APS pairing `(η + 2·sf)` is identically 0. -/
theorem APS_pairing_is_identically_zero
    (Ngen : ℕ) (MR : ℝ) (h : 0 < MR) :
    APS_pairing_majorana Ngen MR h = 0 :=
  APS_pairing_majorana_eq_zero Ngen MR h

/-- **Tier 1 — central verdict (DEGENERATE).**  In the J-self-
    conjugate sub-block, the η-invariant, the net spectral flow, and
    the Bismut–Freed combination are all identically 0.  None equals 8. -/
theorem central_verdict (Ngen : ℕ) (MR : ℝ) (h : 0 < MR) :
    (nuR_spectrum Ngen MR h).etaInvariant = 0 ∧
    totalNetFlow Ngen MR h = 0 ∧
    APS_pairing_majorana Ngen MR h = 0 ∧
    (nuR_spectrum Ngen MR h).etaInvariant ≠ 8 ∧
    totalNetFlow Ngen MR h ≠ 8 ∧
    APS_pairing_majorana Ngen MR h ≠ 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact eta_is_identically_zero Ngen MR h
  · exact spectral_flow_is_identically_zero Ngen MR h
  · exact APS_pairing_is_identically_zero Ngen MR h
  · exact nuR_etaInvariant_ne_eight Ngen MR h
  · exact totalNetFlow_ne_eight Ngen MR h
  · exact APS_pairing_majorana_ne_eight Ngen MR h

/-- **Tier 1 — DEGENERATE verdict in the SM regime.**  For
    `Ngen = 3` and any positive Majorana mass, all candidate quantities
    are exactly 0; the gross crossing count is 6; none is 8. -/
theorem SM_verdict (MR : ℝ) (h : 0 < MR) :
    (nuR_spectrum 3 MR h).etaInvariant = 0 ∧
    totalNetFlow 3 MR h = 0 ∧
    totalGrossCrossings 3 MR h = 6 ∧
    APS_pairing_majorana 3 MR h = 0 ∧
    APS_index_y_R_zero 3 1 MR h = -(3 / 2) ∧
    APS_index_y_R_physical 3 1 MR h = 0 ∧
    -- and none of these matches 8
    (nuR_spectrum 3 MR h).etaInvariant ≠ 8 ∧
    totalNetFlow 3 MR h ≠ 8 ∧
    totalGrossCrossings 3 MR h ≠ 8 ∧
    APS_pairing_majorana 3 MR h ≠ 8 ∧
    APS_index_y_R_zero 3 1 MR h ≠ 8 ∧
    APS_index_y_R_physical 3 1 MR h ≠ 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact nuR_eta_SM MR h
  · exact totalNetFlow_SM MR h
  · exact totalGrossCrossings_SM MR h
  · exact APS_pairing_majorana_eq_zero 3 MR h
  · exact APS_index_SM_y_R_zero MR h
  · exact APS_index_y_R_physical_eq_zero 3 1 MR h
  · exact nuR_etaInvariant_ne_eight 3 MR h
  · exact totalNetFlow_ne_eight 3 MR h
  · exact totalGrossCrossings_SM_ne_eight MR h
  · exact APS_pairing_majorana_ne_eight 3 MR h
  · exact APS_index_y_R_zero_ne_eight 3 1 MR h (by decide)
  · exact APS_index_y_R_physical_ne_eight 3 1 MR h

/-! ## What this means structurally — bullet list -/

/-- **Tier 1 — final standing claim.**  The η-invariant + spectral-flow
    dispatch decisively fails to upgrade the τ^8 reading to a
    structural theorem.  All natural APS-style index candidates on
    the J-self-conjugate sub-block are 0 (or `-Ngen/2`).

    The `8` in `y_R = τ^8` does **NOT** come from this route. -/
theorem final_standing_claim (MR : ℝ) (h : 0 < MR) :
    (∀ Ngen : ℕ, (nuR_spectrum Ngen MR h).etaInvariant = 0) ∧
    (∀ Ngen : ℕ, totalNetFlow Ngen MR h = 0) ∧
    (∀ Ngen : ℕ, APS_pairing_majorana Ngen MR h = 0) ∧
    (APS_index_y_R_physical 3 1 MR h = 0) ∧
    (APS_index_y_R_zero 3 1 MR h = -(3 / 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Ngen; exact nuR_etaInvariant_eq_zero Ngen MR h
  · intro Ngen; exact totalNetFlow_eq_zero Ngen MR h
  · intro Ngen; exact APS_pairing_majorana_eq_zero Ngen MR h
  · exact APS_index_y_R_physical_eq_zero 3 1 MR h
  · exact APS_index_SM_y_R_zero MR h

/-! ## Comparison to the AS-index branch -/

/-- **Tier 1 — joint with AS branch.**  Combining this branch's
    result with `compute/atiyah-singer-J-self-conj`:

      AS_index  = 0   (singlet bundle)
      η         = 0   (Majorana pairing)
      sf        = 0   (symmetric splitting)
      APS bulk  = 0
      APS pair  = 0

    All five candidate "structural integers" from the J-self-conj
    sub-block are 0; none is 8. -/
theorem joint_with_AS_branch (Ngen : ℕ) (ν : ℤ) (MR : ℝ) (h : 0 < MR) :
    AS_index_jsc ν = 0 ∧
    (nuR_spectrum Ngen MR h).etaInvariant = 0 ∧
    totalNetFlow Ngen MR h = 0 ∧
    bulk_S4 ν = 0 ∧
    APS_pairing_majorana Ngen MR h = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact AS_index_jsc_eq_zero ν
  · exact nuR_etaInvariant_eq_zero Ngen MR h
  · exact totalNetFlow_eq_zero Ngen MR h
  · exact bulk_S4_eq_zero ν
  · exact APS_pairing_majorana_eq_zero Ngen MR h

end SpectralPhysics.EtaJSelfConj.Verdict
