import SpectralPhysics.KSRCompactness.KSRCompactnessThm
open SpectralPhysics.KSRCompactness

/-! After removing `instance : TopologicalSpace KSR := ⊥`, a local
discrete topology cannot discharge compactness of an infinite Sobolev
class, and the deleted axiom is gone. Expected: this file does not
compile (`Unknown identifier rellich_kondrachov_trace_class`). -/

instance : TopologicalSpace KSR := ⊥

theorem still_no_axiom : False := by
  have hcpt := rellich_kondrachov_trace_class 2 1 (by norm_num) (by norm_num)
  exact False.elim (by cases hcpt)
