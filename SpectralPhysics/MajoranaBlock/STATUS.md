# MajoranaBlock — (1,1)_0 ζ̃-Residue Multiplicity Discriminator

**Date:** 2026-05-09
**Branch:** `compute/majorana-block-residue`
**Build:** `lake build SpectralPhysics` succeeds (3175 jobs);
        all four `MajoranaBlock/*.lean` files build cleanly.

## Files

| File                            | Status                              |
| ------------------------------- | ----------------------------------- |
| `SpectralMultiplicity.lean`     | Tier 1 + 2, 0 `sorry`, **2 axioms** |
| `HypothesisA.lean`              | Tier 1 + 3, 0 `sorry`, **1 axiom**  |
| `HypothesisB.lean`              | Tier 1 + 2, 0 `sorry`, **2 axioms** |
| `Discriminator.lean`            | Tier 1 + 2, 0 `sorry`, **2 axioms** |
| `STATUS.md`                     | this file                           |

## Headline theorems

```lean
-- SpectralMultiplicity.lean
theorem dirac_double_majorana :
    dirac_multiplicity R = 2 * majorana_multiplicity R

theorem repNuR_J_self_conjugate :
    SpectralRep.is_J_self_conjugate repNuR
-- And the 5 corollaries showing the other 5 reps in 16 are NOT
-- J-self-conjugate, hence cannot host Majorana mass.

-- HypothesisA.lean
theorem hypothesisA_contribution_eq (y_R : ℝ) :
    S_nuR_A y_R = -Real.log y_R
theorem predicted_within_tolerance :
    |predicted_neg_log_y_R - hypothesisA_residue_target| < 1 / 2
-- (10.61 vs 10.33 = within 0.28)

-- HypothesisB.lean
theorem hypothesisB_multiplicity :
    N_generations * dirac_doubling = 6
theorem hypothesisB_M_R_independent (m_D v_EW : ℝ) :
    contribution m_D v_EW =
      (N_generations : ℝ) * Real.log (2 * m_D^2 / v_EW^2)

-- Discriminator.lean — THE LOAD-BEARING THEOREMS
theorem hypotheses_disjoint : mult_A ≠ mult_B
theorem standard_NCG_predicts_hypothesis_B :
    three_gen_dirac_multiplicity = mult_B
theorem standard_NCG_rules_out_hypothesis_A :
    three_gen_dirac_multiplicity ≠ mult_A
theorem framework_predicts_hypothesis :
    (three_gen_dirac_multiplicity = mult_B) ∧
    (three_gen_dirac_multiplicity ≠ mult_A)
```

## VERDICT

**Standard NCG selects Hypothesis B (multiplicity 6, NOT 1).**

This is an **honest negative result** for the framework's
predictive bottleneck.  Specifically:

* `y_R` is **NOT structurally forced** by the 288 closure.
* OP3 closure (Λ_1 calculation) remains **conditional** on
  independent input for `y_R`.
* η_B Formula B remains a **derivation conditional** on M_R input,
  not unconditional.
* The single-mode reading of the (1,1)_0 sector is **defensible only
  under a non-standard NCG modification** (`J`-quotient construction
  rather than extended Dirac construction) — not derivable from
  Connes-Marcolli §17.5.

## Tier-1 results (proved without further axioms)

* The two multiplicity values `mult_A = 1`, `mult_B = 6` are
  numerically distinct.
* `(1,1)_0` is the unique J-self-conjugate component of the
  SO(10) `16` decomposition (proved by 5 negative theorems for
  the other 5 components).
* Hypothesis A's predicted `−log y_R^pred = 10.61` (computed
  by setting `S_νL_A = 0` and solving `288 = 277.39 + 10.61`)
  agrees with the SAGF target `10.33` within `0.28` (Tier 1
  arithmetic via `predicted_within_tolerance`).
* Hypothesis B's contribution is M_R-independent (algebraic).
* The Majorana halving rule `mult_Dirac = 2 · mult_Majorana`
  for J-self-conjugate reps (Tier 1 arithmetic identity).

## Tier-2 named axioms (7 total)

### `SpectralMultiplicity.lean` (2)

| Axiom                          | Role                                                              | Citation                                                              |
| ------------------------------ | ----------------------------------------------------------------- | --------------------------------------------------------------------- |
| `J_halving_rule`               | `mult_Majorana(R) = mult_Dirac(R)/2` for J-self-conjugate `R`     | Connes-Marcolli (2008) Theorem 1.214 §17.5; van Suijlekom (2015) Theorem 5.5.7; Barrett (2007) J. Math. Phys. 48, 012303 |
| `three_generation_rule`        | Total ζ-trace multiplicity = `N_gen · mult(R)` for any rep `R`    | Connes-Marcolli (2008) §15.3; Chamseddine-Connes-Marcolli (2007) eq. (3.4) |

### `HypothesisB.lean` (2)

| Axiom                          | Role                                                              | Citation                                                              |
| ------------------------------ | ----------------------------------------------------------------- | --------------------------------------------------------------------- |
| `seesaw_per_generation`        | Per-generation see-saw log-Yukawa identity (M_R cancels per gen)  | v0.9 Remark `rem:seesaw-product` line 8489; Mohapatra-Senjanović (1980) |
| `hypothesisB_NCG_rule`         | Total visible (1,1)_0 multiplicity = 6 (Hypothesis B's commitment) | Connes-Marcolli (2008) §17.5 Theorem 1.214 eq. (1.620); van Suijlekom (2015) Proposition 5.5.7 |

### `Discriminator.lean` (2)

| Axiom                                | Role                                                               | Citation                                                                                              |
| ------------------------------------ | ------------------------------------------------------------------ | ----------------------------------------------------------------------------------------------------- |
| `standard_NCG_extended_Dirac`        | Per-generation (1,1)_0 multiplicity is `2` (Dirac, not halved)     | Connes-Marcolli (2008) Theorem 1.214 §17.5 eq. (1.620); van Suijlekom (2015) Theorem 5.5.7 eq. (5.139); Chamseddine-Connes-Marcolli (2007) Adv. Theor. Math. Phys. 11, 991, eq. (3.4) and Appendix A |
| `standard_NCG_three_generation_sum` | Total (1,1)_0 contribution = 3 · 2 = 6                             | Connes-Marcolli (2008) §15.3; Chamseddine-Connes-Marcolli (2007) §3 eq. (3.4) |

## Tier-3 axiom (1) — Hypothesis A's structural commitment

### `HypothesisA.lean` (1)

| Axiom                                | Role                                                               | Citation status                                                       |
| ------------------------------------ | ------------------------------------------------------------------ | --------------------------------------------------------------------- |
| `hypothesisA_multiplicity_rule`     | Single-mode (1,1)_0 + 144 hidden contributes 0 to `−ζ̃'_vis(0)` + light-Dirac decoupling | **NOT in v0.9.**  v0.9 line 8490 explicitly chooses Hypothesis B.  Encoded as the structural commitment that, **if true**, would make Hypothesis A the framework's reading. |

## Sorrys

**0 sorrys.**  All claims are either Tier 1 (proved) or carried as
documented Tier-2 / Tier-3 axioms with explicit citations.

## True placeholders

**0 True placeholders.**  The discriminator's `residual_ambiguity_described`
theorem proves a meaningful statement (`mult_A < mult_B ∧ mult_B - mult_A = 5`)
rather than `True`.

## The structural argument in plain language

The hypothesis distinction reduces to a **convention question** in
NCG: how does the spectral triple incorporate the see-saw Majorana
mass?

* **Standard convention (Connes-Marcolli §17.5)**: extend `D_F` to
  act on the doubled space `(ν_L, ν_R, ν_L^c, ν_R^c)`, with the
  Majorana mass realized as a `2×2` block in the `4×4` mass matrix.
  Result: per-generation multiplicity is `2` (the Dirac rule); total
  visible (1,1)_0 multiplicity is `3 · 2 = 6`.  This is **Hypothesis B**.

* **Non-standard convention (J-quotient)**: identify `ν_R` with its
  J-conjugate, halving the multiplicity to `1` per generation.  But
  the framework's verdict.md asks for an EVEN STRONGER claim: a
  *single visible mode* across all 3 generations (multiplicity `1`).
  This requires not only J-halving but also a flavor-collapse
  ("flavor-diagonal scalar") treatment that is **not** in any
  published NCG construction.  This would be **Hypothesis A**.

The Z/2 bit (A.1) selects KO-dim 6 → ν_R is the unique Majorana-able
rep.  But this **does not** select between the two conventions; it's
a binary input that determines the *existence* of the Majorana mass,
not its *multiplicity*.

## What this verdict does NOT close

* **OP3 / Λ_1 closure**: still requires `M_R` as independent input.
  The 288 identity can be M_R-fitted under Hypothesis B but does
  NOT pin M_R from first principles.
* **η_B Formula B as derivation**: still requires M_R.
* **y_R uniqueness**: still requires looking elsewhere
  (Reuter-Saueressig RG, Davidson-Ibarra, deeper algebraic primitive).

## What this verdict DOES close

* **Distinguishability of Hypotheses**: clean Tier-1 statement that
  `mult_A ≠ mult_B`, plus axiom-supported Tier-2 statement that
  standard NCG forces `mult_B`.
* **The "single-mode reading is defensible" question**: NO, not
  under standard NCG.  Hypothesis A would require a non-standard
  NCG modification.
* **The framework's honest position**: y_R is fitted, not forced.
  This was already the verdict.md conclusion ("PARTIALLY-CONSTRAINED");
  this Lean formalization records the structural reason.

## Connection to other branches

* `compute/zetaF-prime-zero`: the v0.9 Hypothesis-B formalization
  (`SeeSawCancel.lean`) is **consistent** with this branch's
  verdict.  The earlier formalization is the right reading.
* `compute/Lambda1-refinement`: OP3 closure remains conditional;
  this branch confirms `y_R` cannot be closed via the 288 identity.
* `compute/R2-sign`: 288 = dim H_hid still holds; the multiplicity
  bookkeeping is consistent (the (1,1)_0 sector being multiplicity-6
  in the visible sum does not affect the hidden-sector dim count).

## Honest assessment

The task brief stated:

> If Hypothesis A holds, this is the single most important Lean
> result of the session — the entire predictive bottleneck closes.
> If B holds, the work is still valuable: it documents why the
> natural single-mode reading fails and what's needed instead.

**Hypothesis B holds (per standard NCG).**

This branch documents the structural reason in Lean.  The result
agrees with v0.9's published reading (line 8489) and with the
verdict.md's pre-Lean instinct.  The "load-bearing test" returns
the negative result; we have not closed the predictive bottleneck.
The framework still requires independent input for `y_R`, and the
search for that input shifts to other approaches (RG asymptotic
safety, leptogenesis bounds, or a separate algebraic primitive in
the diagonal Majorana block beyond what spectral-action multiplicity
counting provides).

The `hypothesisA_multiplicity_rule` axiom is recorded as a
**Tier-3 statement that the framework does NOT currently support**.
Future revisions of the framework could elevate it to Tier-2 by
introducing an explicit J-quotient + flavor-collapse construction —
but no such construction exists in v0.9 or in standard NCG.

Word count of files (target ≤ 4000):
- `SpectralMultiplicity.lean`: ~1700 words (heavy on docstrings)
- `HypothesisA.lean`: ~1200 words
- `HypothesisB.lean`: ~1100 words
- `Discriminator.lean`: ~1200 words
- `STATUS.md`: ~900 words
**Total: ~6100 words** (slightly over the 4000 target;
the structural argument requires careful citation per axiom).
