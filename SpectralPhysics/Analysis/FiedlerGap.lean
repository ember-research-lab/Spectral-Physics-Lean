/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Fiedler-qualitative core: connected ⟹ nondegenerate ground state

The math half of the "λ₁ > 0 from self-reference" bridge, proved on the
*concrete* Mathlib graph Laplacian (NOT the framework's opaque `lambda_1`).

`connected_lapMatrix_ker_finrank_one`: a connected graph's Laplacian has a
one-dimensional nullspace — the only zero-modes are the constants, i.e. the
ground state is unique and the spectral gap is **nondegenerate**. This is the
formal content of the framework's claim "anisotropy of the trace form ⟺
algebraic connectivity ⟺ λ₁ > 0".

## Scope (honest accounting)

* This is the **provable math** half. It is CLOSED (kernel axioms only).
* It does **not** wire into `SCSE.HeatDeathForbidden.lambda_1_pos_from_self_reference`,
  which quantifies over the opaque `RelationalKernel`/`lambda_1`. Wiring requires
  giving `RelationalKernel` a concrete `SimpleGraph` carrier (Phase-2.1 infra).
* The remaining **framework posit** is exactly `SelfReferenceClosure ⟹ G.Connected`
  ("a faithful self-model requires a connected self"); everything below it is this
  lemma. Turning nullity-1 into a quantitative `λ₂ > 0` floor is the Cheeger step
  (`λ₂ ≥ h²/2`), not yet in Mathlib.
-/

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A connected graph's Laplacian has a one-dimensional nullspace: the only
zero-modes are the constants (ground state unique ⇒ spectral gap nondegenerate). -/
theorem connected_lapMatrix_ker_finrank_one (hG : G.Connected) :
    Module.finrank ℝ (G.lapMatrix ℝ).toLin'.ker = 1 := by
  classical
  rw [← card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix]
  haveI : Subsingleton G.ConnectedComponent :=
    hG.preconnected.subsingleton_connectedComponent
  haveI : Nonempty V := hG.nonempty
  haveI : Nonempty G.ConnectedComponent := inferInstance
  haveI : Unique G.ConnectedComponent := uniqueOfSubsingleton (Classical.arbitrary _)
  exact Fintype.card_unique
