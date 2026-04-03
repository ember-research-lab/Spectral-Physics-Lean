/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Minkowski Spacetime Infrastructure

Concrete definitions for 4-dimensional Minkowski spacetime with signature
(-,+,+,+), used as the arena for the Clay Yang-Mills problem statement.

## Main definitions

* `Spacetime`: ℝ⁴ as `EuclideanSpace ℝ (Fin 4)`
* `lorentzInner`: the Lorentz metric η(x,y) = -x⁰y⁰ + x¹y¹ + x²y² + x³y³
* `minkowskiNormSq`: η(x,x)
* `SpacelikeSeparated`: η(x-y, x-y) > 0
* `ForwardLightCone`: {p | p⁰ ≥ 0 ∧ η(p,p) ≤ 0}

## References

* Streater-Wightman, "PCT, Spin and Statistics, and All That" (1964)
* Jaffe-Witten, "Quantum Yang-Mills Theory" (Clay problem statement)
-/

noncomputable section

namespace SpectralPhysics.Minkowski

/-- 4-dimensional spacetime as EuclideanSpace ℝ (Fin 4). -/
abbrev Spacetime := EuclideanSpace ℝ (Fin 4)

/-- Time component x⁰. -/
def timeComponent (x : Spacetime) : ℝ := x 0

/-- Spatial components (x¹, x², x³). -/
def spatialComponent (x : Spacetime) (i : Fin 3) : ℝ := x i.succ

/-- The Lorentz metric η(x,y) = -x⁰y⁰ + x¹y¹ + x²y² + x³y³.
    Signature (-,+,+,+). -/
def lorentzInner (x y : Spacetime) : ℝ :=
  -(x 0 * y 0) + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

/-- Minkowski norm squared η(x,x) = -t² + x² + y² + z². -/
def minkowskiNormSq (x : Spacetime) : ℝ := lorentzInner x x

/-- Two spacetime points are spacelike separated if η(x-y, x-y) > 0.
    (With our (-,+,+,+) convention: spatial distance exceeds time separation.) -/
def SpacelikeSeparated (x y : Spacetime) : Prop :=
  0 < minkowskiNormSq (x - y)

/-- The closed forward light cone V⁺ = {p : p⁰ ≥ 0, η(p,p) ≤ 0}.
    Energy-momentum vectors with non-negative energy and timelike/lightlike. -/
def ForwardLightCone : Set Spacetime :=
  {p | 0 ≤ p 0 ∧ minkowskiNormSq p ≤ 0}

/-! ### Basic lemmas -/

variable (x y : Spacetime)

theorem lorentzInner_comm : lorentzInner x y = lorentzInner y x := by
  simp only [lorentzInner]; ring

theorem spacelikeSeparated_symm :
    SpacelikeSeparated x y ↔ SpacelikeSeparated y x := by
  unfold SpacelikeSeparated minkowskiNormSq lorentzInner
  simp only [WithLp.ofLp_sub, Pi.sub_apply]
  constructor <;> intro h <;> nlinarith

theorem zero_mem_forwardLightCone : (0 : Spacetime) ∈ ForwardLightCone := by
  constructor
  · show 0 ≤ (0 : Spacetime) 0
    simp
  · show minkowskiNormSq 0 ≤ 0
    simp [minkowskiNormSq, lorentzInner]

theorem forwardLightCone_nonempty : Set.Nonempty ForwardLightCone :=
  ⟨0, zero_mem_forwardLightCone⟩

/-- For a pure time vector (t,0,0,0), the Minkowski norm squared is -t². -/
theorem minkowskiNormSq_neg_of_timelike (t : ℝ) :
    let v : Spacetime := WithLp.toLp 2 (fun i : Fin 4 => if i = 0 then t else 0)
    minkowskiNormSq v = -(t ^ 2) := by
  simp [minkowskiNormSq, lorentzInner]
  ring

end SpectralPhysics.Minkowski

end
