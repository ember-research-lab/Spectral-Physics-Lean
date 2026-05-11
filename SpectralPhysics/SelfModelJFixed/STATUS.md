# SelfModelJFixed — Self-Model Deficit Restricted to J-Fixed Points

**Date:** 2026-05-10
**Branch:** `compute/self-model-deficit-J-fixed`
**Build:** `lake build SpectralPhysics` succeeds (3175 jobs).
        Each `SelfModelJFixed/*.lean` file builds cleanly.

## Files

| File                                  | Status                                    |
| ------------------------------------- | ----------------------------------------- |
| `JFixedLocus.lean`                    | Tier 1, **0 sorry**, **0 axioms**         |
| `RestrictedZeta.lean`                 | Tier 1, **0 sorry**, **4 axioms**         |
| `SingleEigenvalueReduction.lean`      | Tier 1, **0 sorry**, **0 axioms**         |
| `Verdict.lean`                        | Tier 1, **0 sorry**, **0 axioms**         |
| `STATUS.md`                           | this file                                 |

**Total: 0 sorry, 0 True placeholders, 4 named axioms (M_R, σ_0).**

## VERDICT

### **NO** under standard NCG; **CONDITIONAL YES** under non-standard
J-quotient reading.

The J-fixed restriction does NOT *naturally* reduce to a
single-eigenvalue equation.  The reduction holds IFF the spectral
multiplicity of `Fix(J) ⊂ H_F` is 1.  Standard NCG (Connes–Marcolli
§17.5) gives multiplicity 6 (3 generations × Dirac doubling),
falsifying the reduction.  Only the non-standard "J-quotient"
reading (Hypothesis A in `compute/majorana-block-residue`) gives
multiplicity 1 — but this requires an axiom not in the manuscript.

### J-fixed multiplicity: **6 (standard NCG) or 1 (non-standard)**

The two readings are arithmetically distinct (`mult_std_ne_quot`).
The framework's standing reading is multiplicity 6 (Hypothesis B,
formalized in `compute/zetaF-prime-zero` and
`compute/majorana-block-residue`).

### Predicted y_R under J-quotient reading

* `−log y_R = 10.61` ⇒ `y_R = exp(-10.61) ≈ 2.45 × 10⁻⁵`
* Empirical SAGF target: `y_R ≈ 3.27 × 10⁻⁵`
* Multiplicative gap: ~25% (predicted is **lower** than empirical)
* `−log y_R` gap: `10.61 − 10.33 = 0.28` (~3% of either value)

This matches `compute/majorana-block-residue.HypothesisA.predicted_within_tolerance`
which records the same `0.28` gap.

## Headline theorems

```lean
-- JFixedLocus.lean
theorem nu_R_unique_J_fixed_in_16 :
    SubRep.is_J_fixed repNu_R ∧
    ¬ SubRep.is_J_fixed repQ_L ∧ ¬ SubRep.is_J_fixed repU_Rc ∧
    ¬ SubRep.is_J_fixed repD_Rc ∧ ¬ SubRep.is_J_fixed repL_L ∧
    ¬ SubRep.is_J_fixed repE_Rc

theorem mult_std_eq_six : mult_std = 6
theorem mult_quot_eq_one : mult_quot = 1
theorem mult_std_ne_quot  : mult_std ≠ mult_quot

-- RestrictedZeta.lean
def reduces_to_single_eigenvalue (m : ℕ) : Prop := m = 1
theorem std_does_not_reduce  : ¬ reduces_to_single_eigenvalue mult_std
theorem quot_does_reduce     : reduces_to_single_eigenvalue mult_quot
theorem reduction_iff_quot (m : ℕ) :
    reduces_to_single_eigenvalue m ↔ m = mult_quot

-- SingleEigenvalueReduction.lean
theorem prediction_within_half :
    |predicted_neg_log_y_R - empirical_neg_log_y_R| < 1 / 2
theorem std_fails_majorana_bound :
    (residual_value : ℝ) / 6 < majorana_lower_bound
theorem quot_satisfies_majorana_bound :
    majorana_lower_bound ≤ predicted_neg_log_y_R
theorem reduction_summary :
    -- (quot reduces) ∧ (std fails Majorana) ∧ (quot satisfies Majorana)

-- Verdict.lean — THE LOAD-BEARING THEOREM
theorem verdict :
    ((residual_value : ℝ) / (mult_std : ℝ) < majorana_lower_bound) ∧
    (majorana_lower_bound ≤ (residual_value : ℝ) / (mult_quot : ℝ)) ∧
    (mult_std ≠ mult_quot)

theorem final_standing_claim :
    -- (ν_R uniquely selected) ∧ (reduction iff mult=1) ∧ (std fails) ∧ (quot succeeds)
```

## Tier-1 results (0 axioms, 0 sorry)

* `nu_R` is the **unique** J-fixed sub-rep of the SO(10) 16
  (proved by 5 negative theorems for the other 5 sub-reps —
  Q_L, u_R^c, d_R^c (color ≠ 1); L_L (Y = -1/2 ≠ 0);
  e_R^c (Y = 1 ≠ 0)).
* The two multiplicity values `mult_std = 6`, `mult_quot = 1` are
  arithmetically distinct.
* The single-eigenvalue equation `m · (−log y_R) = 10.61`
  has Majorana-scale solutions IFF `m = 1`.
* The standard-NCG single-mode equation `(−log y_R) = 10.61/6 ≈ 1.77`
  fails the Majorana lower bound `≥ 8`.
* The J-quotient single-mode equation `(−log y_R) = 10.61` satisfies it.
* The predicted `−log y_R` (10.61) and empirical SAGF target (10.33)
  agree to within 0.28, and the gap is positive (overshoot).

## Named axioms (4 total)

### `RestrictedZeta.lean` (4)

| Axiom        | Role                                          | Citation                          |
| ------------ | --------------------------------------------- | --------------------------------- |
| `M_R`        | The right-handed neutrino Majorana scale      | v0.9 line 8487                    |
| `M_R_pos`    | `M_R > 0`                                     | physical mass                     |
| `sigma0`     | Planck-scale normalization `(12/√(32π)) M_Pl` | v0.9 ratio convention             |
| `sigma0_pos` | `σ_0 > 0`                                     | dimensional positivity            |

These four axioms are **abstract scale parameters**; they enter
only the symbolic decomposition `log M_R = log σ_0 + log y_R` of
`RestrictedZeta.log_M_R_decomp`.  They are NOT needed to state or
prove the verdict (which goes through pure arithmetic on the
rational `residual_value = 1061/100`).  They could be eliminated by
defining `y_R` directly as a positive real parameter, but we keep
them to match the v0.9 dimensional convention.

## Sorrys

**0 sorry** in this branch.  All theorems are proved unconditionally.

## True placeholders

**0 True placeholders.**  Every theorem has an honest content statement.

## Connection to other formalization branches

### Self-Model Deficit (parent identity, `compute/zetaF-prime-zero`)

The headline identity being restricted is

  `−ζ̃'_vis(0) = S_charged + S_νL + S_νR = 277.39 + 184.62 − 174.01 = 288`,

with `S_νL + S_νR = 10.61` the *residual* after the see-saw cancellation.
This branch asks: does the J-fixed restriction account for that
`10.61` as a *single-eigenvalue* term `m · (−log y_R)`?

### Multiplicity discriminator (`compute/majorana-block-residue`)

The branch reuses the same `(mult_A = 1, mult_B = 6)` discriminator,
projected onto the residue `10.61` rather than the integrated
288 closure.  The identifications

  `mult_std_matches_majorana_block_B : mult_std = 6`,
  `mult_quot_matches_majorana_block_A : mult_quot = 1`

are the cross-branch bridges.

### J-self-conjugate AS index (`compute/atiyah-singer-J-self-conj`)

The AS branch returned NEGATIVE: AS chiral index of the J-fixed
locus is 0 because `(1, 1)_0` is a gauge singlet (curvature acts as
zero).  This branch returns NO/CONDITIONAL: the multiplicity reading
that would force `y_R` is non-standard.  Both are consequences of the
same structural fact: J-fixed = gauge-singlet, and gauge singlets do
NOT carry the curvature/multiplicity content needed to force an integer.

### J-self-conjugate η-invariant (`compute/eta-invariant-J-self-conj`)

The η-branch is in parallel and is expected to return NEGATIVE for
the same reason (curvature on a gauge singlet vanishes, so APS-η
contains no anomaly content).

### ζ_F^{ν_R} regularization (`compute/zeta-F-nuR-regularized`)

The remaining route addresses a *different* question (mass formula via
ζ_F, not multiplicity), so its verdict is logically independent.  But
both branches encounter the `mult_std = 6 vs mult_quot = 1` wall.

## What this branch contributes

1. **Type-level statement of the J-fixed locus** (`is_J_fixed`,
   `repNu_R`, `mult_std`, `mult_quot`).
2. **A decidable arithmetic discriminator** between Hypothesis A
   (mult 1) and Hypothesis B (mult 6) projected on `−ζ̃'_vis(0)`.
3. **A Majorana-bound criterion** distinguishing the two readings:
   only Hypothesis A's prediction is in the Majorana scale window;
   Hypothesis B's would force an electroweak-scale `y_R ≈ 0.17`.
4. **The conditional reduction theorem** `reduction_iff_quot`:
   single-eigenvalue closure holds IFF multiplicity = 1.
5. **Honest verdict** `verdict` and `final_standing_claim` matching
   the standard-NCG outcome of `compute/majorana-block-residue`.

## What this branch does NOT contribute

* It does NOT close the y_R bottleneck under standard NCG.
* It does NOT pick between Hypothesis A and Hypothesis B — it
  *records* the discriminator at the level of the residue identity.
* It does NOT formalize the analytic continuation of `ζ_F^{Fix(J)}`
  from `Re(s) > 0` to `s = 0`; it works at the symbolic single-mode
  level (which is what the AS, η, ζ_F branches do too).

## Build status

* `lake build SpectralPhysics` — **succeeds**, 3175 jobs.
* `lake build SpectralPhysics.SelfModelJFixed.JFixedLocus` — succeeds.
* `lake build SpectralPhysics.SelfModelJFixed.RestrictedZeta` — succeeds.
* `lake build SpectralPhysics.SelfModelJFixed.SingleEigenvalueReduction` — succeeds.
* `lake build SpectralPhysics.SelfModelJFixed.Verdict` — succeeds.

## Honest closure on the verdict family

|                                 | Verdict      | Reason                                          |
|---------------------------------|--------------|-------------------------------------------------|
| `atiyah-singer-J-self-conj`     | NEGATIVE     | AS chiral index of singlet = 0                  |
| `eta-invariant-J-self-conj`     | (running)    | Curvature-zero on singlet expected              |
| `zeta-F-nuR-regularized`        | (running)    | Same Hypothesis B vs A discriminator            |
| `self-model-deficit-J-fixed`    | NO/COND      | Reduction requires non-standard J-quotient      |

The pattern: J-self-conjugacy uniquely SELECTS the locus (ν_R), but
none of the spectral-counting machinery (AS, η, ζ) automatically
COLLAPSES the locus to a single eigenvalue.  All three quantitative
routes hit the same multiplicity wall: `6 (std) vs 1 (quot)`.

The y_R bottleneck remains open as a transcendent input.  The
framework's *standing* prediction is the see-saw scale window
`M_R ∈ [10¹⁴, 10¹⁵] GeV` (v0.9 line 8487), which is one-decade-wide
naturalness rather than uniquely fixed.
