import SpectralPhysics.DixonOrderOne.Verdict
open SpectralPhysics.DixonOrderOne

/-- After U8 repair: the zero map still satisfies unconstrained `OrderOne`.
The former axiom is gone; the honest negative is the theorem below. -/
example : OrderOne (fun _ => (0 : OctonionFactor)) LeftMult RightMult :=
  zero_map_orderOne

example : ¬ OrderOneImpliesZerothOrder LeftMult RightMult :=
  dixon_reduction_hypothesis_false

#print axioms zero_map_orderOne
#print axioms dixon_reduction_hypothesis_false
#print axioms dixon_order_one_unconstrained_has_witness
#print axioms dixon_has_nonzero_associator
#print axioms dixon_LR_does_not_commute
