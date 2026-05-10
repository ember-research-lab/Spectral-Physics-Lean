# MajoranaSelfRef — Self-Reference Machinery vs y_R Bottleneck

**Date:** 2026-05-09
**Branch:** `compute/majorana-self-reference`
**Build:** `lake build SpectralPhysics` succeeds (3178 jobs);
        all four `MajoranaSelfRef/*.lean` files build cleanly.

## Files

| File                            | Status                              |
| ------------------------------- | ----------------------------------- |
| `JSelfConjugate.lean`           | Tier 1, 0 sorry, 0 axiom            |
| `TriadicPartition.lean`         | Tier 1, 0 sorry, 0 axiom            |
| `SelfReferenceClosure.lean`     | Tier 1 + Tier 3, 0 sorry, **1 axiom** |
| `Verdict.lean`                  | Tier 1, 0 sorry, 0 axiom            |
| `STATUS.md`                     | this file                           |

## Headline theorems

```lean
-- JSelfConjugate.lean
def isMajorana {Field} (ψ : Field) : Prop := JAction Field ψ ψ
def isDirac {Field} (ψ ψ_c : Field) : Prop :=
    ψ ≠ ψ_c ∧ JAction Field ψ ψ_c
theorem nu_R_isMajorana : isMajorana NuRSector.nu_R
theorem nu_R_is_unique_JSelfConj_in_16 :
    isJSelfConjugate repNu_R ∧
    ¬ isJSelfConjugate repQ_L ∧ ¬ isJSelfConjugate repU_Rc ∧
    ¬ isJSelfConjugate repD_Rc ∧ ¬ isJSelfConjugate repL_L ∧
    ¬ isJSelfConjugate repE_Rc

-- TriadicPartition.lean
theorem fiedler_min_max_ratio_far_from_y_R :
    fiedler_min_max_ratio > 10000 * y_R_target
theorem y_R_bracketed_by_half_powers :
    half_pow_16 < y_R_target ∧ y_R_target < half_pow_14

-- SelfReferenceClosure.lean
theorem tau_pow_8_close_to_y_R :
    tau_pow_8 < 2 * y_R_target ∧ y_R_target < 2 * tau_pow_8
theorem tau_pow_7_too_large : tau_pow_7 > 3 * y_R_target
theorem tau_pow_9_too_small : tau_pow_9 < y_R_target / 3
theorem S_struct_close_to_target :
    |S_struct - neg_log_y_R_target| < 1 / 3

-- Verdict.lean — load-bearing summary
theorem structural_verdict :
    GaugeRep.isJSelfConjugate repNu_R ∧
    (tau_pow_8 < 2 * y_R_target ∧ y_R_target < 2 * tau_pow_8) ∧
    (tau_pow_7 > 3 * y_R_target ∧ tau_pow_9 < y_R_target / 3)
```

## VERDICT

### **PARTIAL.**

Self-reference machinery:

* **identifies** the y_R locus (J-self-conjugate sector — uniquely
  ν_R among the SO(10) `16` sub-reps),
* **constrains** y_R magnitudinally (the τ^8 coincidence brackets
  y_R within factor 2; the additive `9 + φ ≈ 10.62` matches
  `−ln(y_R) ≈ 10.33` within 1/3),
* **does not derive** the exponent uniquely (alternative integer
  exponents 7 and 9 fail by factor 3, but the choice 8 is not
  forced by primitives).

A clean negative — that self-reference machinery cannot in principle
pin y_R — is **not** what this branch establishes.  What is
established: **self-reference machinery is structurally aligned with
empirical y_R**, but the alignment is **insufficient to be a
derivation**.  The honest classification is **PARTIAL**.

## What's needed to upgrade PARTIAL → YES

A **structural derivation of the exponent** (8 in Probe 2, the
additive 7+δ in Probe 3).  Candidates not in this branch:

* **Atiyah–Singer index** for the J-self-conjugate sector of `D_F`.
* **η-invariant** of the spectral triple restricted to (1,1)_0.
* **Zeta-determinant decomposition**: an explicit calculation of
  `−ζ̃'_vis(0)` restricted to J-fixed points yielding the exponent
  `8` from a structural count.
* **Self-Model Deficit refinement**: a stronger version of the
  288 identity that, when restricted to the J-self-conjugate
  sector, gives a single eigenvalue equation.

## Tier-1 results (proved without further axioms)

* `(1,1)_0` is the unique J-self-conjugate component of the SO(10)
  `16` decomposition (proved by 5 negative theorems for the other 5
  components, plus 1 positive theorem for ν_R).
* The Majorana / Dirac dichotomy is structurally disjoint
  (`majorana_dirac_disjoint`).
* The triadic 1:2 Fiedler partition gives an order-1 asymmetry, not
  the order-`10⁻⁵` y_R: `fiedler_min_max_ratio > 10000 · y_R_target`.
* No power `(1/2)^n` for `n ≤ 10` lands within factor 25 of y_R.
* `τ^8 ∈ (2.8 × 10⁻⁵, 4.0 × 10⁻⁵)` brackets y_R = 3.27 × 10⁻⁵
  within factor 2.
* `τ^7 > 3 · y_R` (too large by factor 3); `τ^9 < y_R / 3` (too
  small by factor 3) — the integer exponent 8 is the *unique*
  match in {7, 8, 9}, but is not derived.
* `S_struct = 9 + φ ≈ 10.618` matches `−ln(y_R) ≈ 10.33` within
  `1/3`.

## Tier-2 named axioms

**0 in Tier 1 / Tier 2.**  All structural facts are derived.

## Tier-3 axioms (1) — conjectural identifications

### `SelfReferenceClosure.lean` (1)

| Axiom                              | Role                                                     | Citation status                                                              |
| ---------------------------------- | -------------------------------------------------------- | ---------------------------------------------------------------------------- |
| `y_R_self_reference_conjecture`    | The conjectural identification `y_R = τ^8`              | **NOT a theorem.**  Numerical coincidence (`τ^8` matches y_R within 5%).  Records the conjecture for downstream use IF/WHEN the exponent is derived.  Cited: `pre_geometric/y_r_chirality_unification/survey.md` §6. |

This axiom is recorded as a **Tier-3 statement that the framework
does NOT currently support** — it is the structural commitment of
the τ^8 reading that, *if true*, would give `y_R = τ^8`.  It is
**not used** by the load-bearing `structural_verdict` theorem in
`Verdict.lean`.  It is included only to document the conjecture in
Lean for future derivation work.

## Sorrys

**0 sorrys.**  All claims are either Tier 1 (proved) or carried as
the documented Tier-3 conjectural axiom with explicit citation.

## True placeholders

**0 True placeholders.**  All theorems prove meaningful statements.

## Numerical coincidences in Lean

The branch establishes the following **structurally aligned
numerical facts** as Tier-1 lemmas:

| Quantity                      | Value (bracket)            | Empirical y_R / target           | Match factor        |
| ----------------------------- | -------------------------- | -------------------------------- | ------------------- |
| `1/2` (Fiedler 1:2)           | exact `0.5`                | y_R = 3.27e-5                    | factor `1.53e+4` ✗ |
| `1/3` (Fiedler symdiff)       | exact `0.333…`             | y_R = 3.27e-5                    | factor `1.02e+4` ✗ |
| `(1/2)^15`                    | exact `1/32768 ≈ 3.05e-5` | y_R = 3.27e-5                    | factor `0.93`       |
| `τ^7`                         | bracket `> 1.0e-4`         | y_R = 3.27e-5                    | factor `> 3` ✗     |
| `τ^8`                         | bracket `(2.8e-5, 4.0e-5)`| y_R = 3.27e-5                    | **factor `~1.05`** ✓ |
| `τ^9`                         | bracket `< 1.1e-5`         | y_R = 3.27e-5                    | factor `< 0.34` ✗  |
| `9 + φ` (additive)            | bracket `(10.617, 10.62)` | `−ln(y_R) ≈ 10.33`              | factor `~1.03`      |

The `τ^8` and `9+φ` rows are the **structurally aligned
coincidences**.  Both are equivalent (both give y_R ≈ 3.4e-5).
But the exponent `8` (resp. additive `7 + (2+φ)`) is **not derived**.

## Honest dual reading

The fact that **four** different structural primitives give close
fits within factor 2 of y_R (τ^8 = 1.05x; (1/2)^15 = 1.07x; λ^7
= 1.15x; φ^-22 = 1.29x — see `chirality_check.py`) is **suspicious**:
it suggests the bracket `[2 × 10⁻⁵, 6 × 10⁻⁵]` is wide enough that
any exponential of a primitive number will fall in it for some
nearby integer exponent.

This branch does NOT resolve the dual reading.  The current state
is consistent with both:

* (i) **The framework's primitives "want" to land near y_R**
   (supporting the structural reading).
* (ii) **The bracket is wide enough that any exponential fit
   succeeds** (refuting the structural reading as derivative).

Discriminating between (i) and (ii) is **the substantive
research question** flagged for follow-up.

## Connection to other branches

* **`compute/majorana-block-residue` (closed)**: standard NCG
  multiplicity gives 6 (Hypothesis B), not 1.  This branch confirms
  that result is consistent with PARTIAL: standard NCG does not
  pin y_R, and self-reference machinery does not pin y_R either,
  but for *different* reasons (multiplicity vs exponent).

* **`compute/zetaF-prime-zero`**: the `SeeSawCancel.lean` framework
  is consistent with this branch's verdict.  See-saw cancellation
  is M_R-independent (line 8489); y_R magnitude must come from
  elsewhere.

* **`compute/Lambda1-refinement`**: OP3 closure remains conditional
  on independent input for y_R.  This branch extends the
  PARTIALLY-CONSTRAINED classification to the self-reference
  vocabulary.

## Recommended path forward

Given the PARTIAL state, the most productive next step is **NOT** to
manufacture a positive y_R derivation, but to:

1. **Tier-classify y_R as a transcendent IC** analogous to the
   (A.1) bit (`pre_geometric/ko_dim6_inputs/verdict.md`).  Both
   would then be initial conditions of the spectral-action
   evolution, not derivable from the algebra.

2. **Pursue a leptogenesis / Davidson–Ibarra argument**: the
   framework's η_B = λ^14 derivation ties η_B to Wolfenstein
   cycle structure.  *If* y_R = λ^7, then η_B = (y_R)^2 = λ^14
   follows — closing two coincidences at once.

3. **Investigate Reuter–Saueressig RG fixed point**: if
   asymptotic safety gives y_R independently and agrees with
   τ^8, that would be an independent confirmation.

4. **Search for the structural exponent**: Atiyah-Singer index
   on the J-self-conjugate sector, or zeta-determinant
   decomposition; if either yields exponent `8`, the PARTIAL
   verdict upgrades to YES.

## Word count

* `JSelfConjugate.lean`: ~1100 words (definitions + 6 sub-rep theorems)
* `TriadicPartition.lean`: ~600 words (1:2 partition refutation)
* `SelfReferenceClosure.lean`: ~1500 words (3 probes)
* `Verdict.lean`: ~1000 words (structural summary)
* `STATUS.md`: ~1000 words

**Total: ~5200 words.**

## Final word

The user's hypothesis — that y_R lives in self-reference machinery
rather than standard see-saw geometry — is **structurally aligned**
with the empirical value (τ^8 within 5%, 9+φ within 1/3 of `−ln y_R`).

But the alignment is **not yet derivative**.  The exponent `8` is the
gap.  The branch's load-bearing theorem (`structural_verdict` in
`Verdict.lean`) records the partial state honestly:

```lean
theorem structural_verdict :
    GaugeRep.isJSelfConjugate repNu_R ∧
    (tau_pow_8 < 2 * y_R_target ∧ y_R_target < 2 * tau_pow_8) ∧
    (tau_pow_7 > 3 * y_R_target ∧ tau_pow_9 < y_R_target / 3)
```

(1) the locus is identified, (2) the magnitude is constrained,
(3) the exponent uniquely brackets — but uniqueness is a
*numerical bracket*, not a *derivation*.  The verdict is **PARTIAL**.

This is the honest follow-up to `compute/majorana-block-residue`'s
negative result for Hypothesis A.  Self-reference machinery does
not "save" y_R — it identifies the right locus and constrains the
magnitude, but the path to a unique derivation requires further
structural work (index theory / zeta-determinant / asymptotic safety)
that is **not** in this branch and **not** in v0.9.
