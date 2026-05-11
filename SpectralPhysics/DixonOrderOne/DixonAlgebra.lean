/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Algebra.CayleyDickson
import SpectralPhysics.Algebra.Hurwitz
import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.Quaternion

/-!
# The Dixon Algebra and its non-associative structure

The Dixon algebra is `A_Dixon := ℂ ⊗_ℝ ℍ ⊗_ℝ 𝕆`.  Its non-associativity
is entirely concentrated in the `𝕆 = CayleyDickson ℍ` factor.  For the
Connes order-one axiom, the obstruction is at the level of left- and
right-multiplications, and only the `𝕆`-factor obstructs them from
commuting.  We therefore work in this module with the *octonion factor*
`𝕆 := CayleyDickson (Quaternion ℝ)` directly; the tensor structure adds
nothing to the obstruction (left- and right-multiplication by elements
of `ℂ ⊗ ℍ` automatically commute because that factor is associative).

This file:

* Defines `OctonionFactor := CayleyDickson (Quaternion ℝ)` with notation `𝕆`.
* Defines `LeftMult a : 𝕆 → 𝕆` and `RightMult b : 𝕆 → 𝕆`.
* Defines the `associator a x b := (a * x) * b - a * (x * b)`.
* Proves that the associator measures the failure of `L_a` and `R_b`
  to commute on a vector `x` (this is the *whole point* of the
  associator).
* Provides an explicit witness `i * j ≠ j * i` in `Quaternion ℝ`,
  which combined with `CayleyDickson.not_assoc_of_not_comm` yields
  a non-zero associator in `𝕆`.

## References

* Baez, J., *The Octonions* (2002), §2 — non-associativity of 𝕆.
* Bochniak, A., Sitarz, A., *Spectral interaction between universes*,
  arXiv:2001.02613, *Class. Quantum Grav.* 38 (2021) 035012 — explicit
  treatment of non-associativity in the Dixon-type spectral triples.
* Boyle, L., Farnsworth, S., *The standard model, the Pati-Salam model,
  and "Jordan geometry"*, arXiv:1910.11888 — order-one violation for
  non-associative finite spectra.
* Connes, A., *Noncommutative Geometry*, §VI — formulation of the
  order-one axiom for associative (real or complex) spectral triples.
-/

namespace SpectralPhysics.DixonOrderOne

open CayleyDickson

/-- The octonion factor of the Dixon algebra:
`𝕆 := CD(ℍ)`, i.e. `CayleyDickson (Quaternion ℝ)`.

We localise the non-associativity obstruction here.  The Dixon algebra
itself is `ℂ ⊗_ℝ ℍ ⊗_ℝ 𝕆`; the `ℂ ⊗ ℍ` factor is associative and so
the order-one obstruction is detected at this level. -/
abbrev OctonionFactor : Type := CayleyDickson (Quaternion ℝ)

/-- Left multiplication by `a`: `L_a x := a * x`. -/
def LeftMult (a : OctonionFactor) : OctonionFactor → OctonionFactor :=
  fun x => a * x

/-- Right multiplication by `b`: `R_b x := x * b`. -/
def RightMult (b : OctonionFactor) : OctonionFactor → OctonionFactor :=
  fun x => x * b

@[simp] theorem LeftMult_apply (a x : OctonionFactor) :
    LeftMult a x = a * x := rfl

@[simp] theorem RightMult_apply (b x : OctonionFactor) :
    RightMult b x = x * b := rfl

/-- The associator `[a, x, b] := (a * x) * b - a * (x * b)`.

In an associative algebra this is identically zero; in `𝕆` it is
identically zero only when at least one of `a, x, b` lies in a real
associative subalgebra.  Generic elements give nonzero associators. -/
def associator (a x b : OctonionFactor) : OctonionFactor :=
  (a * x) * b - a * (x * b)

/-- The associator measures exactly the failure of `R_b` and `L_a`
to commute on `x`.

This is the algebraic heart of the order-one obstruction:
`(L_a ∘ R_b - R_b ∘ L_a) x = [a, x, b]`. -/
theorem associator_eq_commutator_LR (a x b : OctonionFactor) :
    LeftMult a (RightMult b x) - RightMult b (LeftMult a x) = - associator a x b := by
  simp [LeftMult, RightMult, associator]

/-! ## Explicit non-commutative witness in `Quaternion ℝ`

We exhibit `i * j ≠ j * i` in the standard quaternions.  Mathlib's
`Quaternion R` is `QuaternionAlgebra R (-1) 0 (-1)`, so
`i = ⟨0,1,0,0⟩` and `j = ⟨0,0,1,0⟩` give `i*j = k`, `j*i = -k`. -/

/-- The quaternion `i := ⟨0, 1, 0, 0⟩`. -/
def quatI : Quaternion ℝ := ⟨0, 1, 0, 0⟩

/-- The quaternion `j := ⟨0, 0, 1, 0⟩`. -/
def quatJ : Quaternion ℝ := ⟨0, 0, 1, 0⟩

/-- The quaternion `k := ⟨0, 0, 0, 1⟩`. -/
def quatK : Quaternion ℝ := ⟨0, 0, 0, 1⟩

theorem quatI_mul_quatJ : quatI * quatJ = quatK := by
  unfold quatI quatJ quatK
  ext <;> simp

theorem quatJ_mul_quatI : quatJ * quatI = -quatK := by
  unfold quatJ quatI quatK
  ext <;> simp

/-- **Tier 1.**  Quaternions are non-commutative: `i * j ≠ j * i`. -/
theorem quaternion_not_commutative :
    ∃ a b : Quaternion ℝ, a * b ≠ b * a := by
  refine ⟨quatI, quatJ, ?_⟩
  rw [quatI_mul_quatJ, quatJ_mul_quatI]
  -- Goal: quatK ≠ -quatK.  Project to the imK component.
  intro h
  have hk : quatK.imK = (-quatK).imK := congrArg QuaternionAlgebra.imK h
  -- quatK.imK = 1, (-quatK).imK = -1
  unfold quatK at hk
  simp at hk
  -- hk : (1 : ℝ) = -1
  linarith

/-! ## Non-associativity of the octonion factor

This follows from `CayleyDickson.not_assoc_of_not_comm` applied to the
quaternion witness above. -/

/-- **Tier 1.**  The octonion factor `𝕆 = CD(ℍ)` is non-associative:
there exist `x, y, z : 𝕆` with `x * (y * z) ≠ (x * y) * z`.

Proof: combine the quaternion non-commutativity witness
(`i * j ≠ j * i`) with the Cayley-Dickson lemma stating that the
double of a non-commutative algebra is non-associative.  This is the
classical Hurwitz / Baez observation that exactly one application of
CD beyond a non-commutative base loses associativity. -/
theorem octonion_factor_not_associative :
    ∃ x y z : OctonionFactor, x * (y * z) ≠ (x * y) * z := by
  exact CayleyDickson.not_assoc_of_not_comm quaternion_not_commutative

/-- **Tier 1.**  There exist `a, x, b : 𝕆` with non-zero associator.

This is the witness that drives the order-one obstruction. -/
theorem associator_nonzero_witness :
    ∃ a x b : OctonionFactor, associator a x b ≠ 0 := by
  obtain ⟨x, y, z, hne⟩ := octonion_factor_not_associative
  -- hne : x * (y * z) ≠ (x * y) * z
  -- associator x y z = (x * y) * z - x * (y * z)
  refine ⟨x, y, z, ?_⟩
  intro hzero
  apply hne
  have : (x * y) * z = x * (y * z) := by
    have := sub_eq_zero.mp hzero
    -- `(x * y) * z - x * (y * z) = 0` ↔ `(x * y) * z = x * (y * z)`
    exact this
  exact this.symm

/-- **Tier 1.**  At the same witness, left- and right-multiplications
on `𝕆` fail to commute. -/
theorem LR_commutator_nonzero_witness :
    ∃ a b x : OctonionFactor, LeftMult a (RightMult b x) ≠ RightMult b (LeftMult a x) := by
  obtain ⟨a, x, b, h_assoc⟩ := associator_nonzero_witness
  refine ⟨a, b, x, ?_⟩
  intro hcomm
  apply h_assoc
  -- From associator_eq_commutator_LR : L_a R_b x - R_b L_a x = -associator a x b
  -- so if L_a R_b x = R_b L_a x then associator a x b = 0.
  have h := associator_eq_commutator_LR a x b
  rw [hcomm, sub_self] at h
  -- h : 0 = - associator a x b
  -- ⇒ associator a x b = 0
  have hneg : -associator a x b = 0 := h.symm
  exact neg_eq_zero.mp hneg

end SpectralPhysics.DixonOrderOne
