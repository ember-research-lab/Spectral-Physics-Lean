/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Audit.Core
import SpectralPhysics.Audit.FiniteShadows
import SpectralPhysics.GR.ImmirziParameter
import SpectralPhysics.SeeleyDeWitt.GraphDirac

/-!
# Audit.Controls — positive and negative controls for the three checks (NNR-20260922-10)

Every expected detection is pinned with `#guard_msgs`. The build therefore stays green while the
checker flags what it must, and it breaks if a check stops flagging (or starts flagging a clean case).
Each check has a positive control that must fire and a negative control that must not (the G6 witness
that both outcomes are reachable on the production code path).

Real targets:
* `ImmirziParameter.gamma`: the manuscript's `thm:immirzi` is retagged (2026-09-22) as a back-solve
  against S = A/4 (ABCK value; superseded by Domagała–Lewandowski / Meissner).
* `ImmirziParameter.immirzi_from_black_hole`: statement `True := trivial`.
* `GraphDirac.eff_graphDirac`: "graph Dirac `d + d*` on vertices ⊕ edges; continuum `Λ⁰ ⊕ Λ¹`".
  That identification exists only in the docstring and is false (Tier 0).
-/

namespace SpectralPhysics.Audit.Controls

open SpectralPhysics.ImmirziParameter SpectralPhysics.SeeleyDeWitt.GraphDirac SpectralPhysics.Audit.Shadow

/-! ## Check 1 — circular prediction -/

audit_datum gamma "BH-entropy S=A/4"

/-- Synthetic one-hop chain: the check is transitive. -/
noncomputable def gammaTwice : ℝ := 2 * gamma
theorem gammaTwice_pos : 0 < gammaTwice := by unfold gammaTwice; linarith [immirzi_pos]

audit_prediction immirzi_from_black_hole "BH-entropy S=A/4"
audit_prediction gammaTwice_pos "BH-entropy S=A/4"
-- negative control: same tag, no dependence on `gamma`
audit_prediction immirzi_su2_origin "BH-entropy S=A/4"

/--
error: CIRCULAR: prediction SpectralPhysics.ImmirziParameter.immirzi_from_black_hole ("BH-entropy S=A/4") depends on datum SpectralPhysics.ImmirziParameter.gamma
CIRCULAR: prediction SpectralPhysics.Audit.Controls.gammaTwice_pos ("BH-entropy S=A/4") depends on datum SpectralPhysics.ImmirziParameter.gamma
-/
#guard_msgs in
#audit_circularity

/-! ## Check 2 — name ≠ object (bridge with a finite shadow) -/

/--
error: BRIDGE REFUTED: SpectralPhysics.SeeleyDeWitt.GraphDirac.eff_graphDirac — "graph d + d* on vertices ⊕ edges has the heat content of scalar ⊕ Hodge 1-forms": its finite shadow is false (kernel-checked by decide)
-/
#guard_msgs in
audit_bridge eff_graphDirac "graph d + d* on vertices ⊕ edges has the heat content of scalar ⊕ Hodge 1-forms"
  shadow (mul D D = blockDiag L0 L1hodge)

-- negative control: the correct identity is witnessed
/-- info: audit_bridge: SpectralPhysics.Audit.Shadow.graphDirac_square_eq_down WITNESSED -/
#guard_msgs in
audit_bridge graphDirac_square_eq_down "(d + d*)² = L₀ ⊕ L₁^down on vertices ⊕ edges"
  shadow (mul D D = blockDiag L0 L1down)

/-! ## Check 3 — physics-free theorem -/

/--
error: PHYSICS-FREE: SpectralPhysics.ImmirziParameter.immirzi_from_black_hole re-typechecks with SpectralPhysics.ImmirziParameter.gamma replaced by an arbitrary value
-/
#guard_msgs in
#audit_uses immirzi_from_black_hole gamma

-- negative control: positivity uses gamma's definition
/-- info: audit_uses: SpectralPhysics.ImmirziParameter.immirzi_pos USES SpectralPhysics.ImmirziParameter.gamma -/
#guard_msgs in
#audit_uses immirzi_pos gamma

-- honest limitation: check 3 does NOT catch the GraphDirac mislabel (the theorem really uses its values)
/-- info: audit_uses: SpectralPhysics.SeeleyDeWitt.GraphDirac.a2_graphDirac USES SpectralPhysics.SeeleyDeWitt.GraphDirac.oneForm -/
#guard_msgs in
#audit_uses a2_graphDirac oneForm

/-! ## Check 4 — literal laundering (a copied number has no dependency edge) -/

/-- A number pasted from an external script: provenance invisible to the closure walk. -/
noncomputable def launderedValue : ℝ := 609 / 10000
theorem launderedValue_pos : 0 < launderedValue := by unfold launderedValue; norm_num

/--
error: UNDECLARED-LITERAL: SpectralPhysics.Audit.Controls.launderedValue_pos depends on SpectralPhysics.Audit.Controls.launderedValue
-/
#guard_msgs in
#audit_literals launderedValue_pos

audit_input launderedValue "MEASURED: synthetic control"

-- negative control: once provenance is declared the check passes
/-- info: audit_literals: every hard-coded number in the closure has declared provenance -/
#guard_msgs in
#audit_literals launderedValue_pos

end SpectralPhysics.Audit.Controls
