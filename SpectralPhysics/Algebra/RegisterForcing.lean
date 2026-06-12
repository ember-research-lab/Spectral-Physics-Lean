import SpectralPhysics.Algebra.CayleyDickson

/-! # The self-observation register: (ℤ₂)³ from the Cayley–Dickson involution stack

Formalizes the register-forcing upgrade (manuscript selection-corank session
notes §14.7, 2026-06-12): each Cayley–Dickson doubling adjoins exactly one new
conjugation involution (`⟨a,b⟩ ↦ ⟨a,−b⟩`, the "view this factor conjugated"
bit).  Three doublings ℝ → ℂ → ℍ → 𝕆 therefore equip the octonion model
`CD³(ℝ)` with a register of `2³ = 8` commuting sign-views — the discrete
microstate count `M = 8` that dresses tolerance-saturated transfers
(Cabibbo correction `(1 + τ/8)`, thm:cabibbo).

## What is PROVED here (no new axioms)

* `flipTop` (the involution adjoined by one doubling) is an involution, and
  lifts of involutions are involutions — the three register generators
  `t₁, t₂, t₃` on `CD³(ℝ)` square to the identity.
* The generators **commute pairwise** — the register is abelian, `(ℤ₂)³`.
* **Trace register-blindness**: the real part `re : CD³(ℝ) → ℝ` is invariant
  under every register generator — definitionally (`rfl`).  This is the
  algebraic upgrade of the "generation-blind σ" argument: only the
  register-symmetric (democratic) channel can couple to the trace.
* **Faithfulness readouts**: each generator `t_k` negates the level-`k`
  imaginary unit `u_k` and fixes the other two — the three register bits are
  independently observable, so the eight register elements act distinctly.
* `2³ = 8`: the register cardinality equals `dim 𝕆`.

## What is NOT claimed here

* Termination at three bits (no fourth involution) is the Hurwitz/sedenion
  zero-divisor theorem — see `Algebra/Forcing.lean`
  (`tower_terminates_by_zero_divisors`) and `Algebra/Hurwitz.lean`; not
  restated here.
* The KO-dimension-6 chirality inheritance (`J γ = −γ J` ⟹ the chirality
  bit is not an independent register bit) is spectral-triple content
  (manuscript tex @9850); not formalized here.
* The *engagement rule* (why second-order capacity partitions democratically
  over the register, giving `τ²/8`) is the remaining open derivation step
  (open:cabibbo-discrete); nothing here asserts it.

## References

* Ben-Shalom, *Spectral Physics* v1.0, thm:cabibbo + selection-corank session
  notes §14.7 (`spectral_physics/selection_corank/`).
* Baez, *The Octonions*, §2.2 (Cayley–Dickson construction).
-/

namespace SpectralPhysics.Algebra.RegisterForcing

open CayleyDickson

universe u

variable {A : Type u}

/-! ## The doubling involution and its lift -/

/-- The involution adjoined by ONE Cayley–Dickson doubling: view the new
factor conjugated, `⟨a, b⟩ ↦ ⟨a, −b⟩`.  (This is `star` with the inner
conjugation stripped — the *new* bit only.) -/
def flipTop [Neg A] (x : CayleyDickson A) : CayleyDickson A :=
  ⟨x.fst, -x.snd⟩

/-- Push a base-level map through a doubling, componentwise. -/
def lift (f : A → A) (x : CayleyDickson A) : CayleyDickson A :=
  ⟨f x.fst, f x.snd⟩

@[simp] theorem flipTop_fst [Neg A] (x : CayleyDickson A) :
    (flipTop x).fst = x.fst := rfl
@[simp] theorem flipTop_snd [Neg A] (x : CayleyDickson A) :
    (flipTop x).snd = -x.snd := rfl
@[simp] theorem lift_fst (f : A → A) (x : CayleyDickson A) :
    (lift f x).fst = f x.fst := rfl
@[simp] theorem lift_snd (f : A → A) (x : CayleyDickson A) :
    (lift f x).snd = f x.snd := rfl

/-- `flipTop` is an involution. -/
theorem flipTop_flipTop [NonAssocRing A] (x : CayleyDickson A) :
    flipTop (flipTop x) = x := by
  ext <;> simp

/-- Lifting preserves involutivity. -/
theorem lift_invol {f : A → A} (hf : ∀ a, f (f a) = a)
    (x : CayleyDickson A) : lift f (lift f x) = x := by
  ext <;> simp [hf]

/-- `flipTop` commutes with the lift of any odd map (`f (−a) = −f a`). -/
theorem flipTop_lift_comm [NonAssocRing A] {f : A → A}
    (hf : ∀ a, f (-a) = -f a) (x : CayleyDickson A) :
    flipTop (lift f x) = lift f (flipTop x) := by
  ext <;> simp [hf]

/-- `flipTop` is odd. -/
theorem flipTop_neg [NonAssocRing A] (x : CayleyDickson A) :
    flipTop (-x) = -flipTop x := by
  ext <;> simp

/-- Lifts of odd maps are odd. -/
theorem lift_neg [NonAssocRing A] {f : A → A}
    (hf : ∀ a, f (-a) = -f a) (x : CayleyDickson A) :
    lift f (-x) = -lift f x := by
  ext <;> simp [hf]

/-! ## The three-level tower and its register -/

/-- One doubling of ℝ: the complex model. -/
abbrev CD1 := CayleyDickson ℝ
/-- Two doublings: the quaternion model. -/
abbrev CD2 := CayleyDickson CD1
/-- Three doublings: the octonion model. -/
abbrev CD3 := CayleyDickson CD2

/-- Register generator from the THIRD doubling (ℍ → 𝕆). -/
def t3 : CD3 → CD3 := flipTop
/-- Register generator from the SECOND doubling (ℂ → ℍ), pushed up. -/
def t2 : CD3 → CD3 := lift flipTop
/-- Register generator from the FIRST doubling (ℝ → ℂ), pushed up twice. -/
def t1 : CD3 → CD3 := lift (lift flipTop)

/-- **Each register generator is an involution.** -/
theorem t3_invol (x : CD3) : t3 (t3 x) = x := flipTop_flipTop x
theorem t2_invol (x : CD3) : t2 (t2 x) = x :=
  lift_invol (fun a => flipTop_flipTop a) x
theorem t1_invol (x : CD3) : t1 (t1 x) = x :=
  lift_invol (lift_invol (fun a => flipTop_flipTop a)) x

/-- **The register generators commute pairwise.** -/
theorem t3_t2_comm (x : CD3) : t3 (t2 x) = t2 (t3 x) := by
  unfold t3 t2; ext <;> simp [lift, flipTop]
theorem t3_t1_comm (x : CD3) : t3 (t1 x) = t1 (t3 x) := by
  unfold t3 t1; ext <;> simp [lift, flipTop]
theorem t2_t1_comm (x : CD3) : t2 (t1 x) = t1 (t2 x) := by
  unfold t2 t1; ext <;> simp [lift, flipTop]

/-! ## Trace register-blindness (the §14.7 headline, now algebra) -/

/-- The real part of the three-level tower. -/
def re (x : CD3) : ℝ := x.fst.fst.fst

/-- **The trace cannot see any register bit** — definitionally. -/
theorem re_t3 (x : CD3) : re (t3 x) = re x := rfl
theorem re_t2 (x : CD3) : re (t2 x) = re x := rfl
theorem re_t1 (x : CD3) : re (t1 x) = re x := rfl

/-! ## Faithfulness readouts: the three bits are independently observable -/

/-- Level-1 imaginary unit (the `i` of the innermost doubling, pushed up). -/
def u1 : CD3 := ⟨⟨⟨0, 1⟩, 0⟩, 0⟩
/-- Level-2 imaginary unit (the `j` of the second doubling, pushed up). -/
def u2 : CD3 := ⟨⟨0, 1⟩, 0⟩
/-- Level-3 imaginary unit (the `ℓ` of the third doubling). -/
def u3 : CD3 := ⟨0, 1⟩

theorem t1_u1 : t1 u1 = -u1 := by
  unfold t1 u1; ext <;> simp [lift, flipTop]
theorem t2_u1 : t2 u1 = u1 := by
  unfold t2 u1; ext <;> simp [lift, flipTop]
theorem t3_u1 : t3 u1 = u1 := by
  unfold t3 u1; ext <;> simp [flipTop]

theorem t1_u2 : t1 u2 = u2 := by
  unfold t1 u2; ext <;> simp [lift, flipTop]
theorem t2_u2 : t2 u2 = -u2 := by
  unfold t2 u2; ext <;> simp [lift, flipTop]
theorem t3_u2 : t3 u2 = u2 := by
  unfold t3 u2; ext <;> simp [flipTop]

theorem t1_u3 : t1 u3 = u3 := by
  unfold t1 u3; ext <;> simp [lift, flipTop]
theorem t2_u3 : t2 u3 = u3 := by
  unfold t2 u3; ext <;> simp [lift, flipTop]
theorem t3_u3 : t3 u3 = -u3 := by
  unfold t3 u3; ext <;> simp [flipTop]

/-- The readouts are non-degenerate: `u_k ≠ −u_k`. -/
theorem u1_ne_neg : u1 ≠ -u1 := by
  intro h
  have : (1 : ℝ) = -1 := congrArg (fun x : CD3 => x.fst.fst.snd) h
  norm_num at this

/-! ## The count -/

/-- The register has exactly `2³ = 8` elements — `log₂ dim 𝕆` bits.  (Each
element is a choice of "conjugated or not" per doubling level; faithfulness
of the action is witnessed by the readout lemmas above.) -/
theorem register_card : Fintype.card (Fin 3 → Bool) = 8 := by decide

/-- `8 = 2^{N_doublings}` with `N_doublings = 3` — the same `8 = 2^{N_g}`
that enters the Cabibbo discrete correction `(1 + τ/8)` (thm:cabibbo),
provided the generation↔doubling correspondence (conj:three-gen-triality)
is interpretive, not load-bearing: the COUNT rides on the tower alone. -/
theorem register_count_eq_microstates : (2 : ℕ) ^ 3 = 8 := by norm_num

end SpectralPhysics.Algebra.RegisterForcing
