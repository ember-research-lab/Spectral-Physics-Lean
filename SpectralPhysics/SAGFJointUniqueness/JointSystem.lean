/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom

# JointSystem — combine ONLY the substantive constraints

This file conjoins the **5 substantive constraints** defined in
`Constraints.lean` into a single predicate
`JointConstraintSystem v`.  No tautologies.

The shape:

  `JointConstraintSystem v ↔ S1 ∧ S2 ∧ S3 ∧ S4 ∧ S5`

  S1 = SCSE                (depends on `M_R`)
  S2 = Dirac product       (depends on `m_D`)
  S3 = solar splitting     (depends on `(m_D, M_R)`)
  S4 = atmospheric         (depends on `(m_D, M_R)`)
  S5 = Planck Σm_ν         (depends on `(m_D, M_R)`)

This is **5 substantive constraints in 4 free parameters**
`(M_R, m_{D,1}, m_{D,2}, m_{D,3})` (the lightest neutrino mass
`m_1` is derived as `m_{D,1}^2 / M_R`).

The honest decomposition:

* `S1`        depends on `M_R` only (the SCSE root).
* `S2`        depends on `(m_{D,1}, m_{D,2}, m_{D,3})` only.
* `S3, S4, S5` couple `(m_D, M_R)` via the see-saw.

5 substantive equations in 4 unknowns is generically *over*-determined,
but the SCSE's `M_R`-dependence and the splittings' `(m_D, M_R)` coupling
admit a one-parameter family parametrised by `m_1` — see v0.9
`rem:m1-sensitivity` (line 8497-8499) and our `UniquenessTheorem.lean`.
-/

import SpectralPhysics.SAGFJointUniqueness.Constraints

noncomputable section

namespace SpectralPhysics.SAGFJointUniqueness

open Real

/-- **The substantive SAGF joint constraint system**.

Conjunction of the 5 substantive constraints S1-S5.  No tautologies
included; the prior `constraint_288 ∧ constraint_etaB ∧
constraint_sigma0_MPl ∧ constraint_LambdaC` conjuncts have been
dropped as they hold for every `JointValuation` by definition. -/
def JointConstraintSystem (v : JointValuation) : Prop :=
  constraint_SCSE v ∧
  constraint_DiracProduct v ∧
  constraint_dm2_21 v ∧
  constraint_dm2_31 v ∧
  constraint_Planck v

/-! ## Decomposition by parameter dependence -/

/-- The `M_R`-only sub-system (one substantive equation: SCSE). -/
def MR_only (v : JointValuation) : Prop := constraint_SCSE v

/-- The Dirac-product sub-system (one substantive equation, in `m_D` only). -/
def mD_only (v : JointValuation) : Prop := constraint_DiracProduct v

/-- The `(m_D, M_R)`-mixed sub-system (three substantive constraints:
two splittings + Planck inequality). -/
def mD_MR_mixed (v : JointValuation) : Prop :=
  constraint_dm2_21 v ∧ constraint_dm2_31 v ∧ constraint_Planck v

/-- The joint system splits cleanly into three independent sectors:
SCSE alone, Dirac product alone, and the `(m_D, M_R)`-coupled splittings/Planck. -/
theorem joint_decomposes (v : JointValuation) :
    JointConstraintSystem v ↔ MR_only v ∧ mD_only v ∧ mD_MR_mixed v := by
  unfold JointConstraintSystem MR_only mD_only mD_MR_mixed
  constructor
  · intro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · intro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩

/-! ## Sanity — every conjunct of `JointConstraintSystem` is substantive

We record that each conjunct of `JointConstraintSystem` genuinely
restricts `JointValuation`s.  Together these certify that the
`JointConstraintSystem` predicate is **not** definitionally `True`.
-/

/-- The joint system is not vacuously true: the witness valuation
`(MR = 1, mD = (1,1,1))` violates the Dirac-product conjunct, hence
the conjunction. -/
theorem JointConstraintSystem_not_vacuous :
    ¬ JointConstraintSystem witnessFails := by
  intro h
  exact constraint_DiracProduct_substantive h.2.1

end SpectralPhysics.SAGFJointUniqueness

end
