import SpectralPhysics.KSRCompactness.Verdict
import SpectralPhysics.BasinConnectivity.Verdict
open SpectralPhysics.KSRCompactness SpectralPhysics.BasinConnectivity

/-! U1 after: no global topology; compactness is a hypothesis.
These `#print axioms` elaborations quantify over `[TopologicalSpace KSR]`. -/

#print axioms ksr_compact
#print axioms ksr_subset_compact
#print axioms ksr_compact_inter_closed
#print axioms ksr_invariant_sobolev_compact
#print axioms KSR_compactness_verdict
#print axioms KSR_compactness_verdict_constructive
#print axioms coercive_sublevels_compact
#print axioms v092_G3_verdict
#print axioms SAGF_basin_closure_from_hypotheses
