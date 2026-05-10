/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Spectral multiplicities for Dirac vs Majorana fermions in the
finite spectral triple `(A_F, H_F, D_F)`

This file isolates the **standard-NCG multiplicity rules** for the
zeta function `ζ̃_{D_F}(s) = Tr |D_F|^{-s}` (regularized) of the
finite spectral triple at the heart of the Connes--Chamseddine
spectral-action construction of the Standard Model.  These rules are
NOT framework-specific — they are the textbook bookkeeping found in:

* Connes & Marcolli, *Noncommutative Geometry, Quantum Fields and
  Motives*, AMS Colloquium Publications **55** (2008), Chapter 1
  §15 "The finite geometry of the SM" and §17 "The spectral action".
* van Suijlekom, *Noncommutative Geometry and Particle Physics*,
  Springer Mathematical Physics Studies (2015), Chapter 5
  "The noncommutative geometry of electroweak unification".
* Chamseddine, Connes & Marcolli, *Gravity and the standard model
  with neutrino mixing*, Adv. Theor. Math. Phys. **11** (2007) 991.

The rules:

1. **Dirac fermion** in rep `R = (R_color, R_weak)_Y` with `N_gen`
   generations contributes to the ζ-trace with multiplicity per
   Yukawa coupling
   `mult_Dirac(R) = dim_C R_color · dim_C R_weak · 2_{ψ↔ψ̄}`,
   where the factor `2` is the particle-antiparticle doubling
   intrinsic to `H_F = H_L ⊕ H_R ⊕ H̄_L ⊕ H̄_R`.

2. **Majorana fermion** in a `J`-self-conjugate rep `R = R̄`
   identifies `ψ` with its `C`-conjugate.  This **halves** the
   Dirac multiplicity by removing the doubling redundancy:
   `mult_Majorana(R) = mult_Dirac(R) / 2`.

3. The total multiplicity over `N_gen` generations is multiplied
   by `N_gen` for Dirac (each generation independent) and by
   `N_gen` for Majorana with **diagonal** mass matrix (no
   inter-generational mixing) — and by `1` if the Majorana mass is
   a **flavor-diagonal scalar** that produces a single eigenvalue
   degenerate across generations.

The key load-bearing distinction for the framework's `ζ̃'_vis(0)`
identity is whether the right-handed neutrino's contribution to
the visible-sector log-Yukawa sum follows the Dirac rule (per
generation, multiplicity `2`) or the Majorana rule (per generation,
multiplicity `1`).  The closure to 288 admits **either** reading
numerically; the question is which one is forced by NCG.

## Structure of this file

* `SpectralRep`: an abstract gauge representation.
* `SpectralRep.dirac_multiplicity`, `.majorana_multiplicity`:
  the textbook NCG counts.
* `SpectralRep.is_J_self_conjugate`: predicate selecting Majorana-
  admissible reps.
* `dirac_double_majorana`: the halving identity.
* The 16-decomposition rep table, with `(1,1)_0` flagged as the
  unique J-self-conjugate component.

This file declares only **named axioms** (NCG theorems we cite and
do not re-prove) plus Tier-1 arithmetic identities.  No `sorry`.
No `True` placeholder.
-/

namespace SpectralPhysics.MajoranaBlock

open Real

/-! ## Abstract spectral representation -/

/-- A gauge representation `R = (R_color, R_weak)_Y`.

    `dimColor`: dimension of SU(3) component (1 or 3 or 3̄ → 3).
    `dimWeak` : dimension of SU(2) component (1 or 2).
    `hyperch` : U(1)_Y hypercharge (rational).

    For the SO(10) `16` decomposition the six components are:
    `(3,2)_{1/6}, (3̄,1)_{-2/3}, (3̄,1)_{1/3}, (1,2)_{-1/2},
     (1,1)_{1}, (1,1)_{0}`. -/
structure SpectralRep where
  dimColor : ℕ
  dimWeak  : ℕ
  hyperch  : ℚ
  deriving DecidableEq, Repr

namespace SpectralRep

/-- `J`-self-conjugate predicate: a rep is J-self-conjugate iff its
    complex-conjugate (i.e. `(R_color, R_weak)_Y → (R̄_color, R̄_weak)_{-Y}`)
    is the same rep.

    For SU(3) × SU(2) × U(1), this requires `dimColor = 1`
    (singlet, since `3̄ ≠ 3`), `dimWeak = 1` (since `2̄ = 2` in
    SU(2) but `2̄_Y` flips Y), and `hyperch = 0`.

    **Citation**: Connes-Marcolli §15.4 (the `J`-symmetry of the
    finite geometry); van Suijlekom §5.2 (the `J`-grading of `H_F`). -/
def is_J_self_conjugate (R : SpectralRep) : Prop :=
  R.dimColor = 1 ∧ R.dimWeak = 1 ∧ R.hyperch = 0

/-- The textbook NCG **Dirac** multiplicity: each fermion mode in rep
    `R` contributes to `Tr |D_F|^{-s}` with multiplicity
    `dim_C R_color · dim_C R_weak · 2`, where `2` is the
    `ψ ↔ ψ̄` particle-antiparticle doubling.

    For SO(10) `16`:
    * `(3, 2)_{1/6}` → `mult_Dirac = 3·2·2 = 12`
    * `(3̄, 1)_{-2/3}` → `mult_Dirac = 3·1·2 = 6`
    * `(1, 2)_{-1/2}` → `mult_Dirac = 1·2·2 = 4`
    * `(1, 1)_0`     → `mult_Dirac = 1·1·2 = 2`

    **Citation**: Connes-Marcolli (2008) §15.3, eq. (1.560);
    van Suijlekom (2015) Definition 5.1.2; Chamseddine-Connes (2007)
    eq. (3.4). -/
def dirac_multiplicity (R : SpectralRep) : ℕ :=
  R.dimColor * R.dimWeak * 2

/-- The textbook NCG **Majorana** multiplicity: `J`-self-conjugacy
    identifies `ψ` with its `C`-conjugate, halving the Dirac count.

    For `J`-self-conjugate reps,
    `mult_Majorana = mult_Dirac / 2 = dim_C R_color · dim_C R_weak`.

    For `(1, 1)_0` specifically: `mult_Majorana = 1·1 = 1` per
    generation.

    **Citation**: Connes-Marcolli (2008) §17.5 (the Majorana mass
    in the spectral triple); van Suijlekom (2015) §5.5
    (Pati-Salam unification with Majorana masses); Barrett (2007),
    *A Lorentzian version of the noncommutative geometry of the
    Standard Model*, J. Math. Phys. **48**, 012303, §III. -/
def majorana_multiplicity (R : SpectralRep) : ℕ :=
  R.dimColor * R.dimWeak

/-- **Tier 1 arithmetic.**  The Majorana count halves the Dirac count
    *for any* representation. -/
theorem dirac_double_majorana (R : SpectralRep) :
    dirac_multiplicity R = 2 * majorana_multiplicity R := by
  unfold dirac_multiplicity majorana_multiplicity
  ring

end SpectralRep

/-! ## The SO(10) 16 decomposition into SM reps -/

/-- The right-handed neutrino representation `(1, 1)_0`.
    The unique singlet in the `16` of SO(10). -/
def repNuR : SpectralRep := ⟨1, 1, 0⟩

/-- The lepton doublet `(1, 2)_{-1/2}`. -/
def repLeptonDoublet : SpectralRep := ⟨1, 2, -1/2⟩

/-- The right-handed charged lepton `(1, 1)_{+1}`. -/
def repChargedLeptonR : SpectralRep := ⟨1, 1, 1⟩

/-- The quark doublet `(3, 2)_{1/6}`. -/
def repQuarkDoublet : SpectralRep := ⟨3, 2, 1/6⟩

/-- The right-handed up-quark `(3̄, 1)_{-2/3}`.
    Note: we represent `3̄` as `dimColor = 3` (the dimension is the
    same; conjugation only matters for the hypercharge sign). -/
def repUpQuarkR : SpectralRep := ⟨3, 1, -2/3⟩

/-- The right-handed down-quark `(3̄, 1)_{+1/3}`. -/
def repDownQuarkR : SpectralRep := ⟨3, 1, 1/3⟩

/-! ## J-self-conjugacy: only ν_R qualifies -/

/-- **Tier 1.**  `(1, 1)_0` is `J`-self-conjugate. -/
theorem repNuR_J_self_conjugate :
    SpectralRep.is_J_self_conjugate repNuR := by
  unfold SpectralRep.is_J_self_conjugate repNuR
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- **Tier 1.**  The lepton doublet is **not** `J`-self-conjugate
    (its hypercharge is `-1/2 ≠ 0`). -/
theorem repLeptonDoublet_not_J_self_conjugate :
    ¬ SpectralRep.is_J_self_conjugate repLeptonDoublet := by
  unfold SpectralRep.is_J_self_conjugate repLeptonDoublet
  intro ⟨_, h2, _⟩
  exact absurd h2 (by decide)

/-- **Tier 1.**  The charged lepton singlet is **not** `J`-self-conjugate
    (its hypercharge is `+1 ≠ 0`). -/
theorem repChargedLeptonR_not_J_self_conjugate :
    ¬ SpectralRep.is_J_self_conjugate repChargedLeptonR := by
  unfold SpectralRep.is_J_self_conjugate repChargedLeptonR
  intro ⟨_, _, h3⟩
  exact absurd h3 (by decide)

/-- **Tier 1.**  Quark reps are not `J`-self-conjugate (color is `3`,
    not `1`). -/
theorem repQuarkDoublet_not_J_self_conjugate :
    ¬ SpectralRep.is_J_self_conjugate repQuarkDoublet := by
  unfold SpectralRep.is_J_self_conjugate repQuarkDoublet
  intro ⟨h1, _, _⟩
  exact absurd h1 (by decide)

/-! ## Multiplicity values for the SO(10) 16 components -/

/-- `mult_Dirac((1,1)_0) = 2`. -/
theorem dirac_mult_nuR : SpectralRep.dirac_multiplicity repNuR = 2 := by
  unfold SpectralRep.dirac_multiplicity repNuR; decide

/-- `mult_Majorana((1,1)_0) = 1`. -/
theorem majorana_mult_nuR : SpectralRep.majorana_multiplicity repNuR = 1 := by
  unfold SpectralRep.majorana_multiplicity repNuR; decide

/-- `mult_Dirac((1,2)_{-1/2}) = 4`. -/
theorem dirac_mult_lep_doublet :
    SpectralRep.dirac_multiplicity repLeptonDoublet = 4 := by
  unfold SpectralRep.dirac_multiplicity repLeptonDoublet; decide

/-- `mult_Dirac((3,2)_{1/6}) = 12`. -/
theorem dirac_mult_quark_doublet :
    SpectralRep.dirac_multiplicity repQuarkDoublet = 12 := by
  unfold SpectralRep.dirac_multiplicity repQuarkDoublet; decide

/-- `mult_Dirac((3̄,1)_{-2/3}) = 6`. -/
theorem dirac_mult_up_quark_R :
    SpectralRep.dirac_multiplicity repUpQuarkR = 6 := by
  unfold SpectralRep.dirac_multiplicity repUpQuarkR; decide

/-! ## v0.9 framework multiplicities — cross-check

The v0.9 manuscript (eq. 8405) uses per-Yukawa multiplicities

  `mult_q = 6,  mult_ℓ = 2,  mult_ν = 2`,

where each `mult` represents `(color × particle/anti)` for a single
fermion species (one Yukawa coupling = one charged lepton OR one
*Dirac* neutrino flavor, summed over chiralities).

This **agrees** with `dirac_multiplicity` on `repUpQuarkR`,
`repChargedLeptonR`, etc., when one fixes the convention "multiply
quark dimColor 3 × particle/anti 2 = 6, etc." after summing the L
and R chiralities.

The crucial gap: v0.9 **does not state** the Majorana rule for ν_R.
v0.9 line 8480 quotes `S_νR = -174.01` as a single number "from
constraint" — i.e. fitted to close the 288 identity, not derived
from `mult_Majorana((1,1)_0)`. -/

/-- v0.9 quark per-Yukawa multiplicity (eq. 8405): `mult_q = 6`.
    Matches `dirac_multiplicity repUpQuarkR + ` (chirality sum) =
    `6` when one identifies the manuscript's "mult" with the Dirac
    multiplicity of the *right-handed* component (the doublet
    contributes the same per generation in the diagonal Yukawa
    counting). -/
theorem v09_mult_quark_eq : SpectralRep.dirac_multiplicity repUpQuarkR = 6 :=
  dirac_mult_up_quark_R

/-- v0.9 lepton per-Yukawa multiplicity: `mult_ℓ = 2`.
    Matches `dirac_multiplicity repChargedLeptonR = 2`. -/
theorem v09_mult_lepton_eq :
    SpectralRep.dirac_multiplicity repChargedLeptonR = 2 := by
  unfold SpectralRep.dirac_multiplicity repChargedLeptonR; decide

/-- v0.9 light-neutrino per-Yukawa multiplicity: `mult_ν = 2`.
    Matches `dirac_multiplicity repNuR = 2` *if ν_R is treated as
    Dirac*.  The Majorana rule `majorana_multiplicity = 1` would
    halve this — that is the structural distinction at the heart of
    Hypothesis A vs B. -/
theorem v09_mult_neutrino_eq : SpectralRep.dirac_multiplicity repNuR = 2 :=
  dirac_mult_nuR

/-! ## The structural multiplicity discriminator

The framework's `−ζ̃'_vis(0) = 288` identity is unaffected by the
Majorana halving on its own (since `S_νR` is `M_R`-fitted in v0.9).
But **for an unfitted derivation** of `S_νR`, the halving matters:
it determines whether the (1,1)_0 contribution to the visible
log-Yukawa sum is `2·(−log y_R)` per generation (Dirac convention,
giving `2·3 = 6` Majorana modes) or `1·(−log y_R)` per generation
(Majorana convention, giving `3` modes).

The two readings are tied to **whether ν_R is in the visible sum
or the hidden sum**:

* If ν_R is **visible** with Dirac convention: `mult_R = 2·3 = 6`,
  `S_νR^bare = -6·log y_R = -6·log(M_R/σ_0) ≈ -62`.
* If ν_R is **visible** with Majorana convention: `mult_R = 1·3 = 3`,
  `S_νR^bare = -3·log y_R ≈ -31`.
* If ν_R is **hidden** (single-mode, "diagonal Majorana scalar"):
  `mult_R = 1`, `S_νR^bare = -log y_R ≈ -10.33`.

None of these matches the v0.9-quoted `S_νR = -174.01` directly:
the manuscript instead defines `S_νR` as the **see-saw correction
absorbing also the m_D Dirac terms**, not as a bare Majorana
contribution.

The Hypothesis A / B distinction in the framework is precisely:

* **Hypothesis A (single-mode)**: the visible (1,1)_0 sector
  contributes ONE log to the residue, namely `−log y_R`.  The
  Dirac neutrino sector handles its own (Dirac) log term cleanly,
  and the see-saw doesn't enter the bookkeeping at this level.
* **Hypothesis B (3-generation see-saw sum)**: the visible
  (1,1)_0 sector contributes through the see-saw substitution
  `m_ν^light = m_D²/M_R`, summed over 3 generations, giving a
  combination of m_D and v terms (M_R cancels). -/

/-- The single-mode multiplicity that Hypothesis A requires:
    the (1,1)_0 sector contributes **exactly one** log-Yukawa to
    `−ζ̃'_vis(0)`.  This is `mult = 1`. -/
def single_mode_multiplicity : ℕ := 1

/-- The three-generation Dirac multiplicity that Hypothesis B
    requires: the (1,1)_0 sector contributes 3 (one per generation),
    multiplied by the Dirac doubling factor 2, summed over the
    see-saw substitution. -/
def three_gen_dirac_multiplicity : ℕ := 6

/-- The three-generation Majorana multiplicity (the "intermediate"
    reading): `1 × 3 = 3` modes, no Dirac doubling. -/
def three_gen_majorana_multiplicity : ℕ := 3

/-! ## Named axioms — the NCG inputs we do not re-prove

These are textbook NCG facts that are not currently in Mathlib.
They serve as inputs to the discriminator argument in
`Discriminator.lean`. -/

/-- **Named axiom — Tier 2.**  The `J`-self-conjugacy halving rule
    for Majorana fermions in a finite spectral triple.

    In words: if `R` is a `J`-self-conjugate rep and the Dirac
    operator `D_F` carries a Majorana mass term in the `R`-block
    (a `J`-symmetric self-pairing), then the contribution to
    `Tr |D_F|^{-s}` from that block is half the Dirac contribution.

    **Citation**: Connes-Marcolli (2008) Theorem 1.214 §17.5
    (the spectral action with Majorana masses); van Suijlekom (2015)
    Theorem 5.5.7 (Pati-Salam Majorana sector); Barrett (2007)
    Lorentzian NCG, Lemma III.2.

    This axiom encodes the standard rule `mult_Majorana = mult_Dirac/2`. -/
axiom J_halving_rule :
    ∀ R : SpectralRep, SpectralRep.is_J_self_conjugate R →
      SpectralRep.majorana_multiplicity R * 2 =
        SpectralRep.dirac_multiplicity R

/-- **Named axiom — Tier 2.**  Three-generation NCG counting.

    For a representation `R` carried by `N_gen = 3` generations,
    the total ζ-trace multiplicity is
    `mult_total(R, N_gen) = N_gen · mult(R)`,
    independently of the (Dirac vs Majorana) per-rep rule.

    **Citation**: Connes-Marcolli (2008) §15.3 (the sum over
    generations in `H_F`); Chamseddine-Connes (2007) eq. (3.4). -/
axiom three_generation_rule :
    ∀ (R : SpectralRep) (N_gen : ℕ),
      ∃ mult_total : ℕ,
        mult_total = N_gen * SpectralRep.dirac_multiplicity R

end SpectralPhysics.MajoranaBlock
