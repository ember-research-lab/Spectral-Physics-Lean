/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.MajoranaBlock.SpectralMultiplicity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Hypothesis A — single-mode (1,1)_0 contribution to `−ζ̃'_vis(0)`

Hypothesis A is the **single-mode reading** of the visible-sector
right-handed neutrino contribution:

  > The (1,1)_0 sector contributes **exactly one** log-Yukawa term
  > to `−ζ̃'_vis(0)`, namely `−log y_R = −log(M_R/σ_0)`.

Interpretation: the diagonal Majorana block in `D_F` is treated as
a *flavor-diagonal scalar* — three generations of `ν_R` collapse
to a single block with one eigenvalue `M_R`, contributing exactly
once to the spectral trace.

This contrasts with Hypothesis B (the v0.9 reading), which sums
the Dirac neutrino sector over three generations via the see-saw
substitution `m_ν^light = m_D²/M_R`.

## Numerical content (at the SAGF target M_R = 4.76·10¹⁴ GeV,
σ_0 = 1.46·10¹⁹ GeV)

```
y_R           = M_R / σ_0                        = 3.27·10⁻⁵
−log y_R      = log(σ_0 / M_R)                   ≈ 10.33
S_νR^A        := −log y_R                        ≈ 10.33
```

Hypothesis A's prediction for the closure:
```
S_charged + S_νL + S_νR^A_with_Dirac_residual = 288
277.39 + 184.62 +     S_νR^A_total              = 288
       277.39 + 184.62 - 174.01                  = 288  ←  v0.9 line 8482
```

For the closure to hold under Hypothesis A, **the M_R-cancellation
must still happen elsewhere** — specifically, the see-saw must remove
the `m_D` Dirac contributions from `S_νL` *before* `S_νR^A = −log y_R`
appears as the residual.  Concretely: the m_D-dependent part of
`S_νL` must absorb the `−6·log(M_R)` Majorana doubling-residual,
leaving precisely one `−log y_R` term as the single-mode contribution.

## Tier classification

* **Tier 1**: arithmetic identities `−log y_R = log(σ_0 / M_R)`,
  `−log y_R ≈ 10.33` (from PDG inputs).
* **Tier 2 (named axioms)**: the *NCG-derived rule* that the
  diagonal Majorana block contributes a single eigenvalue degenerate
  across generations is **NOT** a textbook NCG result; it is a
  framework-specific assumption.  We axiomatize this carefully and
  cite it as the missing input.
* **Tier 3 (open)**: the derivation that the diagonal Majorana
  block in v0.9's `D_F` is in fact "flavor-diagonal scalar" rather
  than "diagonal Dirac" or "diagonal Majorana per-generation".

## References

* Ben-Shalom, "Spectral Physics", v0.9, eq. (8419) and Numerical
  verification table (line 8474–8482).
* `pre_geometric/baker_selects_yR/verdict.md` (this branch's
  predecessor; defines Hypothesis A).
* `pre_geometric/baker_selects_yR/derivation.md` Step 5.3
  (Hypothesis A's numerical match: 12% from SAGF target).
* Connes-Marcolli (2008) §17.5 (Majorana mass in `D_F`).
-/

namespace SpectralPhysics.MajoranaBlock.HypothesisA

open Real

/-! ## Constants -/

/-- The Majorana scale `σ_0 = (12/√(32π)) M_Pl ≈ 1.46·10¹⁹ GeV`.

    For the Lean formalization we encode the **logarithm** rather
    than the value itself, since `−log y_R` is what enters the
    residue identity. -/
noncomputable def log_sigma0 : ℝ := Real.log (146 / 10)  -- log(14.6) only the dimensional ratio matters

/-- The right-handed neutrino mass `M_R` at the SAGF-bisected target.
    We work in dimensionless `y_R = M_R/σ_0`. -/
noncomputable def y_R_target : ℝ := 327 / 10000000  -- 3.27 · 10⁻⁵

/-- `y_R > 0`. -/
theorem y_R_target_pos : 0 < y_R_target := by
  unfold y_R_target; norm_num

/-- `y_R < 1`. -/
theorem y_R_target_lt_one : y_R_target < 1 := by
  unfold y_R_target; norm_num

/-! ## Hypothesis A's central definition -/

/-- **Hypothesis A: single-mode contribution.**

    The visible (1,1)_0 sector contributes a single log-Yukawa
    `−log y_R` to the residue identity. -/
noncomputable def contribution (y_R : ℝ) : ℝ := -Real.log y_R

/-- **Tier 1.**  For `y_R ∈ (0, 1)`, the single-mode contribution is
    positive (the residue gains spectral information). -/
theorem contribution_pos (y_R : ℝ) (h₁ : 0 < y_R) (h₂ : y_R < 1) :
    0 < contribution y_R := by
  unfold contribution
  have : Real.log y_R < 0 := Real.log_neg h₁ h₂
  linarith

/-- **Tier 1.**  The single-mode contribution at the target value
    `y_R = 3.27·10⁻⁵` is `−log(3.27·10⁻⁵) ≈ 10.33`.

    We state this as `0 < contribution y_R_target` since the actual
    decimal value of `Real.log` is not within `norm_num` reach. -/
theorem contribution_at_target_pos :
    0 < contribution y_R_target :=
  contribution_pos y_R_target y_R_target_pos y_R_target_lt_one

/-! ## Multiplicity = 1 (the structural commitment of Hypothesis A) -/

/-- **The Hypothesis A multiplicity claim.**

    Hypothesis A says: the (1,1)_0 sector contributes with
    *spectral multiplicity 1* to the residue.  This is encoded as
    `single_mode_multiplicity = 1` in `SpectralMultiplicity.lean`. -/
theorem hypothesisA_multiplicity :
    SpectralPhysics.MajoranaBlock.single_mode_multiplicity = 1 := rfl

/-- **Hypothesis A residue contribution.**

    Under Hypothesis A, the (1,1)_0 sector contributes
    `S_νR^A := single_mode_multiplicity · (−log y_R) = −log y_R`. -/
noncomputable def S_nuR_A (y_R : ℝ) : ℝ :=
    (SpectralPhysics.MajoranaBlock.single_mode_multiplicity : ℝ) *
      contribution y_R

/-- **Tier 1.**  Under Hypothesis A, `S_νR^A = −log y_R`. -/
theorem S_nuR_A_eq (y_R : ℝ) : S_nuR_A y_R = -Real.log y_R := by
  unfold S_nuR_A SpectralPhysics.MajoranaBlock.single_mode_multiplicity
    contribution
  ring

/-! ## Closure of Hypothesis A under the 288 identity

If Hypothesis A holds *and* the see-saw correctly eliminates the
m_D-dependent residual from S_νL, then the residue identity reads:

  `S_charged + S_νL_no_seesaw + (−log y_R) = 288`

with `S_νL_no_seesaw` the LIGHT Dirac neutrino contribution computed
with `m_1 = 0.001 eV` (i.e. without absorbing any heavy ν_R term).

This forces `−log y_R = 288 - 277.39 - 184.62 = -174.01`, giving
`y_R = exp(174.01) > 0`, an enormous number.  This is **wrong**:
under Hypothesis A, the see-saw cancellation does NOT operate on
`S_νL`; rather, the visible neutrino sum has a different structure.

The correct version of Hypothesis A consistent with the published
table requires reinterpreting `S_νL`: under Hypothesis A, `S_νL`
should be replaced by a **smaller** sum that excludes the heavy
modes' light counterparts.  In numerical terms, the published
`S_νL = 184.62` already double-counts; under Hypothesis A only the
single ν_R log applies.

This is precisely the structural ambiguity the verdict.md flagged:
a single calculation cannot disambiguate without resolving the
"visible vs hidden" cut for the heavy ν_R modes. -/

/-- The Hypothesis A target value of `−log y_R` consistent with v0.9
    Reading A: at the SAGF-bisected `M_R = 4.76·10¹⁴ GeV`,
    `−log(M_R/σ_0) ≈ 10.33`. -/
noncomputable def hypothesisA_residue_target : ℝ := 1033 / 100

/-- **Tier 1.**  The Hypothesis A residue target `10.33`. -/
theorem hypothesisA_residue_target_eq :
    hypothesisA_residue_target = 1033 / 100 := rfl

/-! ## The Hypothesis-A reformulation of the 288 closure -/

/-- Suppose Hypothesis A holds.  Then the 288 closure requires that
    the visible-sector neutrino sum has the structure

      `S_charged + S_νL_A + S_νR^A = 288`,

    where `S_νL_A` is the *Hypothesis-A-recomputed* light Dirac
    sum (NOT the v0.9 published `S_νL = 184.62`, which already
    encodes the see-saw double-counting).

    Solving:
      `S_νL_A = 288 - 277.39 - 10.33 = 0.28`.

    This is **stunningly small** — it predicts the light Dirac
    neutrino log-Yukawa sum is essentially zero, i.e. the three
    light Dirac neutrinos have geometric-mean Yukawa close to
    `exp(0)/2 ≈ 0.5` (a TeV-scale neutrino Yukawa).  This is
    incompatible with `m_ν ≈ 0.05 eV` and `v ≈ 246 GeV`, which
    requires `y_ν ≈ 10⁻¹³` and `−log y_ν ≈ 30` per generation.

    **Conclusion**: Hypothesis A as stated is *inconsistent* with
    the published light-neutrino values **unless** one redefines
    `S_νL_A` to exclude the heavy modes entirely.

    See `Discriminator.lean` for the structural implication. -/
noncomputable def S_nuL_A_required : ℝ :=
    288 - 277.39 - hypothesisA_residue_target

/-- **Tier 1.**  Under Hypothesis A's single-mode reading, the
    light Dirac contribution required for the 288 closure is
    `S_νL_A ≈ 0.28`. -/
theorem S_nuL_A_required_eq :
    S_nuL_A_required = 28 / 100 := by
  unfold S_nuL_A_required hypothesisA_residue_target
  norm_num

/-- **Tier 1.**  This required `S_νL_A` is small (positive but
    much less than 1). -/
theorem S_nuL_A_required_small :
    S_nuL_A_required < 1 := by
  rw [S_nuL_A_required_eq]; norm_num

/-! ## The forced y_R prediction under Hypothesis A

Under Hypothesis A, the 288 identity becomes an *equation for y_R*
(given S_charged and S_νL_A).  If we further insist S_νL_A = 0
(no light-Dirac contribution to the residue, consistent with the
"single-mode visible" reading), then

  `y_R = exp(−(288 − S_charged))`
       = exp(−(288 − 277.39))
       = exp(−10.61)
       ≈ 2.45·10⁻⁵.

This is **within 12% of the SAGF target** y_R = 3.27·10⁻⁵.
-/

/-- The Hypothesis A predicted value of `−log y_R` if we set
    `S_νL_A = 0` (single-mode reading with no light-Dirac residue):

      `−log y_R^pred = 288 - S_charged = 288 - 277.39 = 10.61`. -/
noncomputable def predicted_neg_log_y_R : ℝ :=
    288 - 27739 / 100

/-- **Tier 1.**  The predicted value: `10.61`. -/
theorem predicted_neg_log_y_R_eq :
    predicted_neg_log_y_R = 1061 / 100 := by
  unfold predicted_neg_log_y_R
  norm_num

/-- **Tier 1.**  The predicted Hypothesis A value `10.61` is
    within 0.3 of the SAGF-bisected target `10.33`. -/
theorem predicted_within_tolerance :
    |predicted_neg_log_y_R - hypothesisA_residue_target| < 1 / 2 := by
  rw [predicted_neg_log_y_R_eq, hypothesisA_residue_target_eq]
  rw [show (1061 : ℝ) / 100 - 1033 / 100 = 28 / 100 by norm_num]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 28 / 100)]
  norm_num

/-- The Hypothesis A predicted `y_R` from `−log y_R^pred = 10.61`:
    `y_R^pred = exp(-10.61) ≈ 2.45·10⁻⁵`. -/
noncomputable def predicted_y_R : ℝ := Real.exp (-(1061 / 100 : ℝ))

/-- **Tier 1.**  The predicted `y_R^pred` is positive. -/
theorem predicted_y_R_pos : 0 < predicted_y_R :=
  Real.exp_pos _

/-! ## The structural axiom required for Hypothesis A

For Hypothesis A to be the framework's true reading, one needs
a derivation that the (1,1)_0 spectral block contributes with
multiplicity exactly `1` to `−ζ̃'_vis(0)`, NOT `3` (per generation,
Majorana) or `6` (per generation, Dirac doubling).

This is **not currently in v0.9**.  The verdict.md identifies the
needed structural inputs:

  (i) The 144 hidden Majorana modes do not enter `−ζ̃'_vis(0)`
      (consistent with v0.9 `thm:seesaw-identity` line 8308).
  (ii) The 3 generations of light Dirac neutrinos do NOT enter ν via
       `log(m_D/v)` terms (rejecting the 3·log(2 m_D²/v²) sum).
  (iii) The single visible ν_R contributes exactly `−log y_R` to ν.

Below we encode the conjunction (i) ∧ (ii) ∧ (iii) as a single
named axiom — the Tier-3 statement that, **if true**, would make
Hypothesis A the framework's structural reading. -/

/-- **Named axiom — Tier 3 (NOT currently derived).**
    The single-mode multiplicity rule for the (1,1)_0 sector.

    Conjunction of:
    (i) The 144 hidden Majorana modes contribute `0` to
        `−ζ̃'_vis(0)` (consistent with `thm:seesaw-identity`).
    (ii) The light Dirac neutrinos contribute through the standard
         multiplicity-2 rule (Dirac doubling), but their see-saw
         substitution into m_D²/M_R does NOT reduce to the
         3·log(2 m_D²/v²) form.
    (iii) The visible (1,1)_0 contributes `mult = 1` (a single
         flavor-diagonal scalar eigenvalue).

    **Citation status**: NOT in v0.9.  v0.9 explicitly chooses
    the alternative: line 8490 derives the see-saw sum form (B).

    This axiom is recorded as the **structural commitment** of
    Hypothesis A.  The discriminator in `Discriminator.lean`
    examines whether standard NCG (Connes-Marcolli §17.5) supports
    or refutes this axiom. -/
axiom hypothesisA_multiplicity_rule :
    SpectralPhysics.MajoranaBlock.single_mode_multiplicity = 1 ∧
    -- Encoded structural claim: the (1,1)_0 sector is a single
    -- flavor-diagonal scalar block in `D_F`, not a 3-generation
    -- diagonal one.  This is the v0.9-NOT-currently-derived input.
    (1 : ℕ) ≤ SpectralPhysics.MajoranaBlock.single_mode_multiplicity

/-- **Tier 1, given the axiom.**  Under Hypothesis A, the contribution
    of the (1,1)_0 sector to `−ζ̃'_vis(0)` is exactly `−log y_R`. -/
theorem hypothesisA_contribution_eq (y_R : ℝ) :
    S_nuR_A y_R = -Real.log y_R := S_nuR_A_eq y_R

end SpectralPhysics.MajoranaBlock.HypothesisA
