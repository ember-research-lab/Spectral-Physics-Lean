/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.RMForcesDivisionAlgebras.ReadingA_FormalChain
import SpectralPhysics.RMForcesDivisionAlgebras.ReadingB_TraceState
import SpectralPhysics.RMForcesDivisionAlgebras.ReadingC_NaturalityForcesAlt
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Star.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Data.Real.Basic

/-!
# Counterexample — `A = ℝ × ℝ` Falsifies Division-Algebra Forcing

## The structural falsifier

We exhibit a concrete finite-dimensional ℝ-algebra `A = ℝ × ℝ` (the
direct product algebra) that:

1. **Satisfies Link 1** of the formal chain: a faithful positive
   linear functional exists (the sum-of-components functional).
2. **Is associative** (hence satisfies Link 3 trivially).
3. **Has finite real dimension `2`** (so naively the dimension is
   compatible with `{1, 2, 4, 8}` — yet the algebra is NOT `ℂ`).
4. **Fails Link 2**: no composition norm exists, because `ℝ × ℝ`
   has zero divisors `(1, 0) · (0, 1) = (0, 0)`.
5. **Is NOT a normed division algebra** — in particular, not
   isomorphic to `ℂ` (the Hurwitz tower entry at dimension `2`).

This is the **structural falsification** of the v0.9 claim that
*Axiom 3 alone forces the Hurwitz tower*.  The missing ingredient
is the **composition-norm hypothesis** (Link 2), which Axiom 3 does
not supply.

## Why `ℝ × ℝ` is the right counterexample

* **Smallest possible.**  Dimension 2.  Avoids any matrix-algebra
  overhead.
* **Standard.**  The split-complex / hyperbolic complex numbers
  `ℝ[x]/(x² - 1) ≅ ℝ × ℝ`.  Albert (1947) identifies them as the
  canonical non-division 2-dim ℝ-algebra.
* **Associative.**  So Link 3 is satisfied — the chain failure
  cannot be blamed on the alternativity step.
* **Faithful trace exists.**  The sum functional `(x, y) ↦ x + y`
  is positive on `(x, y) · (x, y) = (x², y²)`.

## References

* Albert, A.A. (1947). "Absolute valued real algebras." Ann. Math. 48.
* Bruck, R.H. & Kleinfeld, E. (1951). "The structure of alternative
  division rings." Proc. AMS 2.
-/

namespace SpectralPhysics.RMForcesDivisionAlgebras

/-! ## The counterexample algebra

`Counterexample := ℝ × ℝ` with componentwise multiplication. -/

/-- The split-complex / direct-product algebra `ℝ × ℝ`. -/
abbrev Counterexample : Type := ℝ × ℝ

/-! ## Property 1 — Faithful trace exists -/

/-- The sum-of-components functional. -/
def sumFunctional : Counterexample → ℝ := fun a => a.1 + a.2

/-- **Tier 1 — `Counterexample` satisfies Link 1.**

The sum functional, applied to `star a * a` (which on `ℝ × ℝ` is
`a * a` since the involution is trivial: real components are
self-adjoint), is non-negative; and it is *positive* on every
nonzero element.

Concretely: `sumFunctional (star a * a) = a.1² + a.2²`, which
vanishes iff both components vanish. -/
theorem counterexample_link1 :
    Link1_FaithfulTrace Counterexample := by
  refine ⟨sumFunctional, ?_, ?_⟩
  · -- Non-negativity
    intro a
    -- Star on ℝ × ℝ is trivial: star a = a (since star on ℝ is identity).
    -- (star a * a).1 = a.1 * a.1, (star a * a).2 = a.2 * a.2.
    have ha1 : (star a * a).1 = a.1 * a.1 := by
      change (star a).1 * a.1 = a.1 * a.1
      have : (star a).1 = star a.1 := rfl
      rw [this, star_trivial]
    have ha2 : (star a * a).2 = a.2 * a.2 := by
      change (star a).2 * a.2 = a.2 * a.2
      have : (star a).2 = star a.2 := rfl
      rw [this, star_trivial]
    show (star a * a).1 + (star a * a).2 ≥ 0
    rw [ha1, ha2]
    have h1 : a.1 * a.1 ≥ 0 := mul_self_nonneg _
    have h2 : a.2 * a.2 ≥ 0 := mul_self_nonneg _
    linarith
  · -- Faithfulness
    intro a ha
    have ha1 : (star a * a).1 = a.1 * a.1 := by
      change (star a).1 * a.1 = a.1 * a.1
      have : (star a).1 = star a.1 := rfl
      rw [this, star_trivial]
    have ha2 : (star a * a).2 = a.2 * a.2 := by
      change (star a).2 * a.2 = a.2 * a.2
      have : (star a).2 = star a.2 := rfl
      rw [this, star_trivial]
    show 0 < (star a * a).1 + (star a * a).2
    rw [ha1, ha2]
    -- a ≠ 0 means a.1 ≠ 0 ∨ a.2 ≠ 0
    have h_ne : a.1 ≠ 0 ∨ a.2 ≠ 0 := by
      by_contra h
      push_neg at h
      exact ha (Prod.ext h.1 h.2)
    have h1 : a.1 * a.1 ≥ 0 := mul_self_nonneg _
    have h2 : a.2 * a.2 ≥ 0 := mul_self_nonneg _
    rcases h_ne with h | h
    · have : 0 < a.1 * a.1 := by positivity
      linarith
    · have : 0 < a.2 * a.2 := by positivity
      linarith

/-! ## Property 2 — Associative (hence Link 3 trivially) -/

/-- **Tier 1 — `Counterexample` is associative.**

Inherited from `Ring (ℝ × ℝ)`. -/
theorem counterexample_associative :
    ∀ a b c : Counterexample, (a * b) * c = a * (b * c) := by
  intro a b c
  exact mul_assoc a b c

/-- **Tier 1 — `Counterexample` satisfies Link 3 (alternativity).**

Associativity implies alternativity trivially. -/
theorem counterexample_link3 :
    Link3_Alternative Counterexample := by
  refine ⟨?_, ?_⟩
  · intro a b; rw [← mul_assoc]
  · intro a b; rw [mul_assoc]

/-! ## Property 3 — Finite dimension 2 -/

/-- **Tier 1 — `Counterexample` is finite-dimensional with dim = 2.** -/
theorem counterexample_finrank :
    Module.finrank ℝ Counterexample = 2 := by
  show Module.finrank ℝ (ℝ × ℝ) = 2
  rw [Module.finrank_prod, Module.finrank_self]

/-! ## Property 4 — Has zero divisors (refutes Link 2 / division-algebra) -/

/-- The "x-axis" element `(1, 0)`. -/
def eX : Counterexample := (1, 0)

/-- The "y-axis" element `(0, 1)`. -/
def eY : Counterexample := (0, 1)

theorem eX_ne_zero : eX ≠ 0 := by
  intro h
  have := congr_arg Prod.fst h
  simp [eX] at this

theorem eY_ne_zero : eY ≠ 0 := by
  intro h
  have := congr_arg Prod.snd h
  simp [eY] at this

/-- **Tier 1 — `Counterexample` has zero divisors.**

`(1, 0) · (0, 1) = (0, 0)` despite both factors being nonzero.
This is the canonical non-division-algebra signature. -/
theorem counterexample_has_zero_divisors :
    ∃ a b : Counterexample, a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 := by
  refine ⟨eX, eY, eX_ne_zero, eY_ne_zero, ?_⟩
  show ((1 : ℝ), (0 : ℝ)) * (0, 1) = 0
  rw [Prod.mk_mul_mk]
  simp

/-- **Tier 1 — `Counterexample` is NOT a division algebra.**

Direct from `counterexample_has_zero_divisors`: in a division
algebra, `a · b = 0 ∧ a ≠ 0 → b = 0`. -/
theorem counterexample_not_division :
    ¬ (∀ a b : Counterexample, a ≠ 0 → b ≠ 0 → a * b ≠ 0) := by
  intro h
  obtain ⟨a, b, ha, hb, hab⟩ := counterexample_has_zero_divisors
  exact h a b ha hb hab

/-! ## Property 5 — Link 2 fails: no composition norm

A composition norm `n : A → ℝ` satisfies `n(a · b) = n(a) · n(b)`,
hence in particular `n(0) = n(eX · eY) = n(eX) · n(eY)`.  If `n` is
*faithful* (i.e., `n(a) = 0 ↔ a = 0`), then `n(eX), n(eY) > 0`,
forcing `n(0) > 0` — but `n(0) = 0` by linearity/positivity.  This
shows **no faithful composition norm** exists on `Counterexample`.

The weak `Link2_CompositionNorm` predicate we stated only asks for a
non-negative norm, not faithfulness.  The honest accounting:

* `Link2_CompositionNorm Counterexample` is **vacuously satisfied**
  by `n = 0` (the trivially-zero norm).  This shows that the
  predicate as stated is *too weak* to be the load-bearing condition.
* The **strong** Link 2, requiring `n(a) = 0 ↔ a = 0`, **fails** —
  this is the actual force of "composition algebra".

We prove the strong-Link-2 negation: -/

/-- **The strong Link-2 predicate**: a *faithful* composition norm. -/
def StrongLink2_FaithfulCompositionNorm (A : Type*) [Mul A] [Zero A] : Prop :=
  ∃ n : A → ℝ,
    (∀ a : A, n a ≥ 0) ∧
    (∀ a : A, n a = 0 ↔ a = 0) ∧
    (∀ a b : A, n (a * b) = n a * n b)

/-- **Tier 1 — `Counterexample` fails the *strong* Link 2.**

No faithful composition norm exists.  Proof: if `n` were such, then
`n(eX) > 0` and `n(eY) > 0` (faithfulness on the nonzero `eX, eY`),
hence `n(eX · eY) = n(eX) · n(eY) > 0`.  But `eX · eY = 0`, so
`n(eX · eY) = n(0) = 0` (also by faithfulness).  Contradiction. -/
theorem counterexample_fails_strong_link2 :
    ¬ StrongLink2_FaithfulCompositionNorm Counterexample := by
  intro ⟨n, _h_nonneg, h_faith, h_mul⟩
  -- n(eX) > 0 and n(eY) > 0
  have hX : n eX ≠ 0 := fun h => eX_ne_zero ((h_faith eX).mp h)
  have hY : n eY ≠ 0 := fun h => eY_ne_zero ((h_faith eY).mp h)
  -- but eX * eY = 0, so n(0) = n(eX) * n(eY) ≠ 0
  have h_prod : n (eX * eY) = n eX * n eY := h_mul eX eY
  have h_zero : eX * eY = (0 : Counterexample) := by
    show ((1 : ℝ), (0 : ℝ)) * (0, 1) = 0
    rw [Prod.mk_mul_mk]; simp
  rw [h_zero] at h_prod
  -- n 0 = 0 from faithfulness
  have h_n_zero : n 0 = 0 := (h_faith 0).mpr rfl
  rw [h_n_zero] at h_prod
  -- So 0 = n eX * n eY, hence n eX = 0 or n eY = 0
  rcases mul_eq_zero.mp h_prod.symm with h | h
  · exact hX h
  · exact hY h

/-! ## Property 6 — Not isomorphic to ℂ (the Hurwitz-tower entry)

The dimension `2` of `Counterexample` is *consistent* with the
Hurwitz set `{1, 2, 4, 8}`, but the v0.9 claim is *stronger*: the
algebra should be **isomorphic** to one of `{ℝ, ℂ, ℍ, 𝕆}`.

`ℝ × ℝ` is **not** isomorphic to `ℂ` as a ring: `ℂ` has no zero
divisors, `ℝ × ℝ` does. -/

/-- **Tier 1 — `Counterexample` is not ring-isomorphic to ℂ.**

Any ring iso preserves zero divisors.  `Counterexample` has them,
`ℂ` does not.  -/
theorem counterexample_not_iso_complex :
    IsEmpty (Counterexample ≃+* ℂ) := by
  rw [isEmpty_iff]
  intro f
  -- Pull a zero divisor of Counterexample back through f
  obtain ⟨a, b, ha, hb, hab⟩ := counterexample_has_zero_divisors
  have hfa : f a ≠ 0 := by
    intro h
    apply ha
    have := f.injective
    apply this
    rw [h, map_zero]
  have hfb : f b ≠ 0 := by
    intro h
    apply hb
    have := f.injective
    apply this
    rw [h, map_zero]
  have : f (a * b) = f a * f b := map_mul f a b
  rw [hab, map_zero] at this
  -- 0 = f a * f b in ℂ, hence f a = 0 or f b = 0
  rcases mul_eq_zero.mp this.symm with h | h
  · exact hfa h
  · exact hfb h

/-! ## Assembly — the headline counterexample -/

/-- **Headline — `Counterexample` satisfies the starting predicates
of the chain but is NOT in the Hurwitz tower (qua isomorphism).**

This is the structural falsification of v0.9's division-algebra
forcing claim.  The chain breaks at the **strong** Link 2.

Specifically:
* (a) Link 1 holds.
* (b) Link 3 holds (associativity ⇒ alternativity).
* (c) `finrank = 2`, so the *numerical* Hurwitz bound is met.
* (d) BUT: no *faithful* composition norm exists, and the algebra
  is not isomorphic to `ℂ`.

Hence Axiom 3 (Reconstruction + Naturality) — as currently
formalized — does **not** force the Hurwitz tower. -/
theorem RM_does_not_force_division_algebras :
    -- Link 1 holds for Counterexample
    Link1_FaithfulTrace Counterexample ∧
    -- Link 3 holds for Counterexample
    Link3_Alternative Counterexample ∧
    -- finrank = 2 (in the numerical tower)
    Module.finrank ℝ Counterexample = 2 ∧
    -- BUT: strong Link 2 fails, and Counterexample is not ≅ ℂ
    ¬ StrongLink2_FaithfulCompositionNorm Counterexample ∧
    IsEmpty (Counterexample ≃+* ℂ) := by
  refine ⟨counterexample_link1, counterexample_link3,
          counterexample_finrank,
          counterexample_fails_strong_link2,
          counterexample_not_iso_complex⟩

end SpectralPhysics.RMForcesDivisionAlgebras
