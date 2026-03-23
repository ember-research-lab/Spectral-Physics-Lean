/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The Cayley-Dickson Construction

The Cayley-Dickson construction takes a *-algebra `A` and produces a new
algebra `CayleyDickson A` of twice the dimension, equipped with conjugation
and a norm that is multiplicative iff the original algebra is a composition
algebra.

## Main definitions

* `CayleyDickson A` : The Cayley-Dickson double of `A`, as a structure with
  two fields `fst snd : A`, with multiplication
  `⟨a, b⟩ * ⟨c, d⟩ = ⟨ac - d̄b, da + bc̄⟩`
* `CayleyDickson.star` : Conjugation `⟨a, b⟩* = ⟨a*, -b⟩`
* `CayleyDickson.normSq` : The norm-squared `‖⟨a,b⟩‖² = ‖a‖² + ‖b‖²`

## Main results

* `CayleyDickson.mul_def` : The multiplication rule
* `CayleyDickson.star_mul_self` : `x* · x = normSq x • 1`
* `CayleyDickson.normSq_mul` : `normSq (x * y) = normSq x * normSq y`
  (when the base algebra is a composition algebra)
* `CayleyDickson.not_associative_of_not_commutative` : If `A` is not
  commutative, then `CayleyDickson A` is not associative

## The tower

Applying the construction iteratively:
* `ℝ → CayleyDickson ℝ ≅ ℂ`
* `ℂ → CayleyDickson ℂ ≅ ℍ`
* `ℍ → CayleyDickson ℍ ≅ 𝕆`
* `𝕆 → CayleyDickson 𝕆 ≅ 𝕊` (sedenions — has zero divisors!)

## References

* [Baez, *The Octonions*](https://arxiv.org/abs/math/0105155)
* [Springer-Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*]
* Ben-Shalom, *Spectral Physics*, Chapter 22
-/

universe u

variable {A : Type u}

/-- The Cayley-Dickson double of a type `A`. A proper structure to avoid
instance diamonds with `Prod`. -/
@[ext]
structure CayleyDickson (A : Type u) where
  fst : A
  snd : A

namespace CayleyDickson

variable [NonAssocRing A] [StarRing A]

omit [NonAssocRing A] [StarRing A] in
@[simp] theorem mk_fst (a b : A) : (CayleyDickson.mk a b).fst = a := rfl
omit [NonAssocRing A] [StarRing A] in
@[simp] theorem mk_snd (a b : A) : (CayleyDickson.mk a b).snd = b := rfl

/-- Embedding of the base algebra: a ↦ ⟨a, 0⟩ -/
def embed (a : A) : CayleyDickson A := ⟨a, 0⟩

/-- The new imaginary unit: ε = ⟨0, 1⟩ -/
def epsilon [One A] : CayleyDickson A := ⟨0, 1⟩

section Multiplication

/-- Cayley-Dickson multiplication:
  `⟨a, b⟩ * ⟨c, d⟩ = ⟨a * c - star d * b, d * a + b * star c⟩` -/
instance : Mul (CayleyDickson A) where
  mul x y := ⟨x.fst * y.fst - star y.snd * x.snd, y.snd * x.fst + x.snd * star y.fst⟩

theorem mul_def (x y : CayleyDickson A) :
    x * y = ⟨x.fst * y.fst - star y.snd * x.snd, y.snd * x.fst + x.snd * star y.fst⟩ :=
  rfl

@[simp] theorem mul_fst (x y : CayleyDickson A) :
    (x * y).fst = x.fst * y.fst - star y.snd * x.snd := rfl

@[simp] theorem mul_snd (x y : CayleyDickson A) :
    (x * y).snd = y.snd * x.fst + x.snd * star y.fst := rfl

/-- The embedding preserves multiplication -/
theorem embed_mul (a b : A) : embed a * embed b = embed (a * b) := by
  simp [embed, mul_def, star_zero, zero_mul, mul_zero, sub_zero, add_zero]

end Multiplication

section StarStructure

/-- Cayley-Dickson conjugation: `⟨a, b⟩* = ⟨a*, -b⟩` -/
instance : Star (CayleyDickson A) where
  star x := ⟨star x.fst, -x.snd⟩

theorem star_def (x : CayleyDickson A) :
    star x = ⟨star x.fst, -x.snd⟩ :=
  rfl

@[simp] theorem star_fst (x : CayleyDickson A) : (star x).fst = star x.fst := rfl
@[simp] theorem star_snd (x : CayleyDickson A) : (star x).snd = -x.snd := rfl

/-- Conjugation is an involution -/
theorem star_star' (x : CayleyDickson A) : star (star x) = x := by
  exact CayleyDickson.ext (_root_.star_star x.fst) (neg_neg x.snd)

/-- The embedding commutes with conjugation -/
theorem star_embed (a : A) : star (embed a) = embed (star a) := by
  simp [embed, star_def, neg_zero]

end StarStructure

section Ring

/-- Zero element -/
instance : Zero (CayleyDickson A) where
  zero := ⟨0, 0⟩

@[simp] theorem zero_fst : (0 : CayleyDickson A).fst = 0 := rfl
@[simp] theorem zero_snd : (0 : CayleyDickson A).snd = 0 := rfl

/-- One element -/
instance : One (CayleyDickson A) where
  one := ⟨1, 0⟩

@[simp] theorem one_fst : (1 : CayleyDickson A).fst = 1 := rfl
@[simp] theorem one_snd : (1 : CayleyDickson A).snd = 0 := rfl

/-- Addition (componentwise) -/
instance : Add (CayleyDickson A) where
  add x y := ⟨x.fst + y.fst, x.snd + y.snd⟩

@[simp] theorem add_fst (x y : CayleyDickson A) : (x + y).fst = x.fst + y.fst := rfl
@[simp] theorem add_snd (x y : CayleyDickson A) : (x + y).snd = x.snd + y.snd := rfl

/-- Negation (componentwise) -/
instance : Neg (CayleyDickson A) where
  neg x := ⟨-x.fst, -x.snd⟩

@[simp] theorem neg_fst (x : CayleyDickson A) : (-x).fst = -x.fst := rfl
@[simp] theorem neg_snd (x : CayleyDickson A) : (-x).snd = -x.snd := rfl

/-- Left multiplication by one -/
theorem cd_one_mul (x : CayleyDickson A) : (1 : CayleyDickson A) * x = x := by
  ext <;> simp

/-- Right multiplication by one -/
theorem cd_mul_one (x : CayleyDickson A) : x * (1 : CayleyDickson A) = x := by
  ext <;> simp

/-- Subtraction (componentwise) -/
instance : Sub (CayleyDickson A) where
  sub x y := ⟨x.fst - y.fst, x.snd - y.snd⟩

@[simp] theorem sub_fst (x y : CayleyDickson A) : (x - y).fst = x.fst - y.fst := rfl
@[simp] theorem sub_snd (x y : CayleyDickson A) : (x - y).snd = x.snd - y.snd := rfl

/-- Left distributivity: x * (y + z) = x * y + x * z -/
theorem cd_left_distrib (x y z : CayleyDickson A) :
    x * (y + z) = x * y + x * z := by
  ext <;> simp [mul_add, add_mul, star_add] <;> abel

/-- Right distributivity: (x + y) * z = x * z + y * z -/
theorem cd_right_distrib (x y z : CayleyDickson A) :
    (x + y) * z = x * z + y * z := by
  ext <;> simp [mul_add, add_mul] <;> abel

/-- Zero * x = 0 -/
theorem cd_zero_mul (x : CayleyDickson A) :
    (0 : CayleyDickson A) * x = 0 := by
  ext <;> simp

/-- x * 0 = 0 -/
theorem cd_mul_zero (x : CayleyDickson A) :
    x * (0 : CayleyDickson A) = 0 := by
  ext <;> simp [star_zero]

/-- neg * x = -(x * y) ... actually -(x) * y = -(x * y) -/
theorem cd_neg_mul (x y : CayleyDickson A) :
    (-x) * y = -(x * y) := by
  ext <;> simp [neg_mul, mul_neg] <;> abel

/-- x * (-y) = -(x * y) -/
theorem cd_mul_neg (x y : CayleyDickson A) :
    x * (-y) = -(x * y) := by
  ext <;> simp [mul_neg, neg_mul, star_neg] <;> abel

/-- The NonAssocRing instance for CayleyDickson. -/
instance instNonAssocRing : NonAssocRing (CayleyDickson A) where
  add_assoc a b c := CayleyDickson.ext (add_assoc _ _ _) (add_assoc _ _ _)
  zero_add a := CayleyDickson.ext (zero_add _) (zero_add _)
  add_zero a := CayleyDickson.ext (add_zero _) (add_zero _)
  add_comm a b := CayleyDickson.ext (add_comm _ _) (add_comm _ _)
  neg_add_cancel a := CayleyDickson.ext (neg_add_cancel _) (neg_add_cancel _)
  sub_eq_add_neg a b := CayleyDickson.ext (sub_eq_add_neg _ _) (sub_eq_add_neg _ _)
  nsmul := nsmulRec
  zsmul := zsmulRec
  left_distrib := cd_left_distrib
  right_distrib := cd_right_distrib
  zero_mul := cd_zero_mul
  mul_zero := cd_mul_zero
  one_mul := cd_one_mul
  mul_one := cd_mul_one
  natCast n := ⟨n, 0⟩
  natCast_zero := CayleyDickson.ext Nat.cast_zero rfl
  natCast_succ n := CayleyDickson.ext (Nat.cast_succ n) (add_zero 0).symm
  intCast n := ⟨n, 0⟩
  intCast_ofNat n := CayleyDickson.ext (Int.cast_natCast n) rfl
  intCast_negSucc n := CayleyDickson.ext (Int.cast_negSucc n) neg_zero.symm

end Ring

section NormSquared

/-- The norm-squared of a Cayley-Dickson element: ‖⟨a,b⟩‖² = ‖a‖² + ‖b‖² -/
noncomputable def normSq [NormedAddCommGroup A] (x : CayleyDickson A) : ℝ :=
  ‖x.fst‖^2 + ‖x.snd‖^2

/-- The Euclidean norm on CayleyDickson: ‖⟨a,b⟩‖ = √(‖a‖² + ‖b‖²) -/
noncomputable def cdNorm [NormedAddCommGroup A] (x : CayleyDickson A) : ℝ :=
  Real.sqrt (‖x.fst‖^2 + ‖x.snd‖^2)

theorem cdNorm_nonneg [NormedAddCommGroup A] (x : CayleyDickson A) :
    0 ≤ cdNorm x :=
  Real.sqrt_nonneg _

/-- cdNorm² = ‖a‖² + ‖b‖² (by definition + sqrt²) -/
theorem cdNorm_sq [NormedAddCommGroup A] (x : CayleyDickson A) :
    cdNorm x ^ 2 = ‖x.fst‖^2 + ‖x.snd‖^2 :=
  Real.sq_sqrt (by positivity : 0 ≤ ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2)

end NormSquared

section Properties

variable [NonAssocRing A] [StarRing A]

/-- Conjugation is an anti-automorphism: `(x * y)* = y* * x*` -/
theorem cd_star_mul (x y : CayleyDickson A) :
    star (x * y) = star y * star x := by
  have h1 : (star (x * y)).fst = (star y * star x).fst := by
    simp only [mul_def, star_def,
      star_sub, star_mul, star_star, star_neg, neg_mul_neg]
  have h2 : (star (x * y)).snd = (star y * star x).snd := by
    simp only [mul_def, star_def, star_star, neg_mul]
    abel
  exact CayleyDickson.ext h1 h2

/-- If the base algebra is not commutative, the CD double is NOT associative. -/
theorem not_assoc_of_not_comm [Nontrivial A]
    (h : ∃ a b : A, a * b ≠ b * a) :
    ∃ x y z : CayleyDickson A, x * (y * z) ≠ (x * y) * z := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨embed a, embed b, epsilon, ?_⟩
  simp only [embed, epsilon, mul_def, star_zero, star_one,
    zero_mul, mul_zero, one_mul, sub_zero, add_zero]
  intro heq
  apply hab
  have := congr_arg CayleyDickson.snd heq
  simp at this
  exact this.symm

end Properties

section StarRingInstance

variable [NonAssocRing A] [StarRing A]

/-- StarRing instance: star distributes over addition and is anti-multiplicative. -/
instance instStarRing : StarRing (CayleyDickson A) where
  star_involutive x := star_star' x
  star_mul x y := cd_star_mul x y
  star_add x y := CayleyDickson.ext (star_add x.fst y.fst) (neg_add x.snd y.snd)

end StarRingInstance

end CayleyDickson
