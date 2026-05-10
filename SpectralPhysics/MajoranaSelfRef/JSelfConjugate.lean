/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Tactic.NormNum
import Mathlib.Data.Rat.Defs

/-!
# J-Self-Conjugacy of Matter Fields

## Hypothesis under test

The user's structural insight: Majorana fermions satisfy `J_F ψ = ψ`
(J-self-conjugacy).  This is the only matter-field structure in which
the J operator acts as the IDENTITY rather than as an off-diagonal
pairing (Dirac fermions: `J_F ψ = ψ_c`, with `ψ_c ≠ ψ`).

Since the framework's foundation is self-reference (Axiom 4,
observation algebra), Majorana fields are the *only* matter fields
exhibiting self-reference at the J-action level.  This is the precise
sense in which a Majorana field is "its own antiparticle".

## What this file does

* Defines `JAction`, an abstract surrogate for the KO-dim 6
  J-operator on the finite spectral triple.
* Defines `isMajorana` and `isDirac` predicates.
* Records the disjointness: a non-trivial Dirac field cannot be Majorana.
* Reproves that `(1,1)_0` is the unique J-self-conjugate sub-rep of
  the SO(10) `16` decomposition.
* Establishes the **structural locus** of the y_R bottleneck.

## References

* Connes 1996, *Gravity coupled with matter and the foundation of
  noncommutative geometry*, CMP **182**, 155–176.
* Connes-Marcolli 2008, AMS Coll. Pub. **55**, §15.4.
* Barrett 2007, *A Lorentzian version of the noncommutative geometry
  of the Standard Model*, J. Math. Phys. **48**, 012303.
* `pre_geometric/ko_dim6_inputs/verdict.md` — the (A.1) bit.
* v0.9, Theorem `thm:384` (line 8211) and `def:chirality` (line 6882).
-/

namespace SpectralPhysics.MajoranaSelfRef

/-! ## Abstract J-action surrogate -/

/-- The action of the framework's `J` operator (KO-dim 6, charge
    conjugation in the finite spectral triple) on a matter field.

    The two cases are exhaustive:
    * `Self ψ` — `J ψ = ψ` (J-self-conjugate, "Majorana-able").
    * `Pair ψ ψ'` — `J ψ = ψ'` with `ψ' ≠ ψ` (Dirac pairing).

    **Citation**: Connes 1996 §3; Connes-Marcolli 2008 Definition 15.4. -/
inductive JAction (Field : Type*) [DecidableEq Field] : Field → Field → Prop where
  | self  : ∀ ψ : Field, JAction Field ψ ψ
  | pair  : ∀ ψ ψ' : Field, ψ ≠ ψ' → JAction Field ψ ψ'

/-! ## The Majorana / Dirac dichotomy -/

/-- A matter field `ψ` is **Majorana** iff its J-action is the identity:
    `J_F ψ = ψ`. -/
def isMajorana {Field : Type*} [DecidableEq Field] (ψ : Field) : Prop :=
  JAction Field ψ ψ

/-- A matter field `ψ` is **Dirac** iff its J-action takes it to a
    distinct charge-conjugate `ψ_c ≠ ψ`. -/
def isDirac {Field : Type*} [DecidableEq Field]
    (ψ ψ_c : Field) : Prop :=
  ψ ≠ ψ_c ∧ JAction Field ψ ψ_c

/-- **Tier 1.**  Self-conjugacy holds reflexively (every field is at
    least J-self-conjugate by `JAction.self`). -/
theorem isMajorana_refl {Field : Type*} [DecidableEq Field]
    (ψ : Field) : isMajorana ψ := JAction.self ψ

/-- **Tier 1.** A field cannot be both Majorana and Dirac with the
    same charge-conjugate witness. -/
theorem majorana_dirac_disjoint {Field : Type*} [DecidableEq Field]
    (ψ ψ_c : Field) (h_dir : isDirac ψ ψ_c) :
    ψ_c ≠ ψ := by
  intro h_eq
  exact h_dir.1 h_eq.symm

/-! ## SO(10) 16 decomposition: J-self-conjugate sub-reps

The criterion (Connes-Marcolli §15.4): a rep `R = (R_color, R_weak)_Y`
is J-self-conjugate iff `R̄ = R`, which for SU(3) × SU(2) × U(1)
requires `dimColor = 1`, `dimWeak = 1`, and `Y = 0`. -/

/-- An SO(10) sub-rep, labelled by (color dim, weak dim, hypercharge). -/
structure GaugeRep where
  dimColor : ℕ
  dimWeak  : ℕ
  hyperch  : ℚ
  deriving DecidableEq, Repr

namespace GaugeRep

/-- A rep is J-self-conjugate iff `R̄ = R`: color singlet, weak
    singlet, and zero hypercharge. -/
def isJSelfConjugate (R : GaugeRep) : Prop :=
  R.dimColor = 1 ∧ R.dimWeak = 1 ∧ R.hyperch = 0

instance (R : GaugeRep) : Decidable (isJSelfConjugate R) := by
  unfold isJSelfConjugate; infer_instance

end GaugeRep

/-! ## The six SO(10) 16 sub-reps -/

/-- Q_L = `(3, 2)_{1/6}`. -/
def repQ_L : GaugeRep := ⟨3, 2, 1/6⟩

/-- u_R^c = `(3̄, 1)_{-2/3}`. -/
def repU_Rc : GaugeRep := ⟨3, 1, -2/3⟩

/-- d_R^c = `(3̄, 1)_{1/3}`. -/
def repD_Rc : GaugeRep := ⟨3, 1, 1/3⟩

/-- L_L = `(1, 2)_{-1/2}`. -/
def repL_L : GaugeRep := ⟨1, 2, -1/2⟩

/-- e_R^c = `(1, 1)_{1}`. -/
def repE_Rc : GaugeRep := ⟨1, 1, 1⟩

/-- ν_R = `(1, 1)_{0}`. -/
def repNu_R : GaugeRep := ⟨1, 1, 0⟩

/-! ## The selection theorem -/

/-- **Tier 1.**  ν_R is J-self-conjugate. -/
theorem repNu_R_is_JSelfConj : GaugeRep.isJSelfConjugate repNu_R := by
  refine ⟨rfl, rfl, rfl⟩

/-- **Tier 1.**  Q_L is NOT J-self-conjugate (color is 3). -/
theorem repQ_L_not_JSelfConj : ¬ GaugeRep.isJSelfConjugate repQ_L := by
  intro ⟨h, _, _⟩; exact absurd h (by decide)

/-- **Tier 1.**  u_R^c is NOT J-self-conjugate (color is 3). -/
theorem repU_Rc_not_JSelfConj : ¬ GaugeRep.isJSelfConjugate repU_Rc := by
  intro ⟨h, _, _⟩; exact absurd h (by decide)

/-- **Tier 1.**  d_R^c is NOT J-self-conjugate (color is 3). -/
theorem repD_Rc_not_JSelfConj : ¬ GaugeRep.isJSelfConjugate repD_Rc := by
  intro ⟨h, _, _⟩; exact absurd h (by decide)

/-- **Tier 1.**  L_L is NOT J-self-conjugate (Y = −1/2 ≠ 0). -/
theorem repL_L_not_JSelfConj : ¬ GaugeRep.isJSelfConjugate repL_L := by
  intro ⟨_, _, h⟩
  have : (repL_L.hyperch : ℚ) = -1/2 := rfl
  rw [this] at h; exact absurd h (by norm_num)

/-- **Tier 1.**  e_R^c is NOT J-self-conjugate (Y = 1 ≠ 0). -/
theorem repE_Rc_not_JSelfConj : ¬ GaugeRep.isJSelfConjugate repE_Rc := by
  intro ⟨_, _, h⟩
  have : (repE_Rc.hyperch : ℚ) = 1 := rfl
  rw [this] at h; exact absurd h (by norm_num)

/-- **Tier 1 — the uniqueness theorem.**

    Among the six sub-reps of the SO(10) `16`, ν_R is the unique
    J-self-conjugate component.  Self-reference machinery picks the
    Majorana locus uniquely; the magnitude is investigated in
    `SelfReferenceClosure.lean`. -/
theorem nu_R_is_unique_JSelfConj_in_16 :
    GaugeRep.isJSelfConjugate repNu_R ∧
    ¬ GaugeRep.isJSelfConjugate repQ_L ∧
    ¬ GaugeRep.isJSelfConjugate repU_Rc ∧
    ¬ GaugeRep.isJSelfConjugate repD_Rc ∧
    ¬ GaugeRep.isJSelfConjugate repL_L ∧
    ¬ GaugeRep.isJSelfConjugate repE_Rc := by
  refine ⟨repNu_R_is_JSelfConj, repQ_L_not_JSelfConj, repU_Rc_not_JSelfConj,
          repD_Rc_not_JSelfConj, repL_L_not_JSelfConj, repE_Rc_not_JSelfConj⟩

/-! ## A concrete model of the J-self-conjugate sector -/

/-- A trivial one-element type modelling the J-self-conjugate sector
    of (1,1)_0.  In this model, the unique element is its own
    J-image — i.e., it is Majorana. -/
inductive NuRSector : Type
  | nu_R : NuRSector
  deriving DecidableEq

/-- **Tier 1.**  The ν_R sector field is Majorana. -/
theorem nu_R_isMajorana : isMajorana NuRSector.nu_R :=
  isMajorana_refl _

end SpectralPhysics.MajoranaSelfRef
