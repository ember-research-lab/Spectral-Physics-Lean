/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.CompositionUniqueness.HypothesisSet
import SpectralPhysics.CompositionUniqueness.AdditiveSatisfies
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Kasparov-Product Spectral Uniqueness (Path A, narrow scope)

This file states the **honest narrow-scope** uniqueness theorem
for unbounded Kasparov-product spectral triples.

## Status: OPEN — Mesland–Rennie / Rosenberg–Schochet / Kassel UNFORMALISED

Mathlib has no unbounded KK-theory and no spectral-triple
infrastructure as of 2026.  What we do here is:

1. Define a witness predicate `KasparovProductWitness` recording
   the assumption "this binary operation on spectra is a
   spectrum-side shadow of an unbounded Kasparov product".
   The 2026-08-18 repair deleted the unsound K1/K2/K3 axioms
   (each derived `False` via `zeroOp`). The 2026-09-06 lane-B
   pass replaced the `is_kk_product : True` shell by `card_mul`; the
   2026-10-04 decision (Spectral-Physics-Lean#9, option 2) replaces that
   by the product-spectrum shape `sq_shape` (card_mul now derived).

2. K2 (Rosenberg–Schochet cancellation) and K3 (Kassel residue)
   remain **explicit hypotheses** of the implication theorems
   below — not axioms, not discharged.

3. The dependent uniqueness verdict is **OPEN**. Mesland–Rennie
   2014/2016, Rosenberg–Schochet 1987, and Kassel 1987/1989 are
   **UNFORMALISED literature**: no Lean transcription of unbounded
   KK, KK-Künneth, or the noncommutative residue is supplied.

The honest scope is: *"IF an operation satisfies `card_mul` (in
the witness) AND K2 AND K3 as hypotheses, THEN it satisfies the
three-condition predicate. Unconditional Kasparov uniqueness is
OPEN."*

## The three named axioms

### K1 — Mesland (2014) / Mesland-Rennie (2016): unbounded Kasparov product
Citation: Mesland, B., "Unbounded bivariant K-theory and
correspondences in noncommutative geometry", arXiv:1304.3802,
*J. Reine Angew. Math.* 691 (2014); Mesland, B., Rennie, A.,
"Nonunital spectral triples and metric completeness in unbounded
KK-theory", arXiv:1502.04520, *J. Funct. Anal.* 271 (2016).

### K2 — Rosenberg-Schochet (1987): KK-Künneth
Citation: Rosenberg, J., Schochet, C., "The Künneth theorem and
the universal coefficient theorem for Kasparov's generalized
K-functor", *Duke Math. J.* 55 (1987), 431–474.

### K3 — Kassel (1987/1989): periodic cyclic Künneth / NC residue
Citation: Kassel, C., "Cyclic homology, comodules, and mixed
complexes", *J. Algebra* 107 (1987), 195–216; Kassel, C., "Le
résidu non commutatif (d'après M. Wodzicki)", *Sém. Bourbaki* 708,
*Astérisque* 177–178 (1989).

## REPAIRED-SOUND (2026-08-18) + OPEN (2026-09-06 lane B)

The three named axioms K1/K2/K3 below **used to be Lean `axiom`s**.
The 2026-08-18 content audit (`lean-content-audit-2026-08-18/REGISTER.md`
U2) compile-verified that each derives `False` independently from the
`zeroOp : BinaryOpOnSpectra := ⟨fun _ _ => (0 : Spectrum)⟩` witness,
because `KasparovProductWitness.is_kk_product` was `: True` and so
placed no real constraint beyond `symm`. Positive control:
`hostile/U2-K1Unsound.lean` (unknown identifiers K1/K2/K3 on current
code — axioms gone).

**2026-08-18 repair**: K1, K2, K3 deleted as axioms; statements
moved to explicit hypothesis parameters.

**2026-09-06**: `is_kk_product : True` still admitted `zeroOp`;
replaced by `card_mul`. **2026-10-04 (Aaron, #9 option 2)**: `card_mul`
strengthened to `sq_shape` (spec D² = λ²+μ²); `card_mul` derived. Not a
formalisation of Mesland–Rennie.
K2 and K3 stay as named hypotheses on the implication theorems.
Uniqueness verdict is **OPEN**; the literature is UNFORMALISED.
`open:kasparov-uniqueness` in the trunk remains open.

## Out of scope

* Lean proof that Kasparov product is the unique binary operation
  matching K1+K2+K3 (broader uniqueness — see
  `BroaderUniquenessOpen.lean`).
* Lean proof that K1+K2+K3 are mutually consistent at the
  spectrum-level shadow.

## References

* Mesland (2014), Mesland-Rennie (2016) — K1.
* Rosenberg-Schochet (1987) — K2.
* Kassel (1987), Kassel (1989 Bourbaki) — K3.
* `pre_geometric/v091_refactor/composition_decision.md` — Path A.
-/

namespace SpectralPhysics.CompositionUniqueness

/-- A `KasparovProductWitness op` records the assertion that the
binary operation `op` on spectra is a spectrum-side shadow of an
unbounded Kasparov product `D = D₁⊗1 + γ⊗D₂`.

Since `D₁⊗1` and `γ⊗D₂` anticommute, `D² = D₁²⊗1 + 1⊗D₂²`, so the
eigenvalues of `D²` are exactly `λ² + μ²` over eigenvalue pairs. The
sign of each eigenvalue of `D` is not determined by the factor spectra
alone, so the shape constraint is stated on squares:

* `symm` — symmetry in the two factors. **SUBSTANTIVE**.
* `sq_shape` — the multiset of squared eigenvalues of `op μ ν` is the
  additive convolution of the squared-eigenvalue multisets of `μ` and
  `ν` (eigenvalues of `D` are `±√(λ²+μ²)`). **SUBSTANTIVE**; this is
  the K1 *content* at spectrum level (2026-10-04, option 2 of
  Spectral-Physics-Lean#9, Aaron).
* `card_mul` is now a **derived theorem**
  (`KasparovProductWitness.card_mul`), not a field.

Mesland–Rennie 2014/2016 (unbounded Kasparov product),
Rosenberg–Schochet 1987 (KK-Künneth), and Kassel 1987/1989
(noncommutative residue) remain **UNFORMALISED literature**. This
structure is not a KK-equivalence predicate.

**WARNING (proved below, `kasparov_witness_K3_inconsistent`)**: this
witness and the `K3` hypothesis (`HamiltonianAdditivity`, trace of
`op μ ν` = additive trace law) are jointly inconsistent, so
`kasparov_product_satisfies_three_conditions` is vacuously true. K3 as
stated is the *additive* Hamiltonian law and does not hold for the
Kasparov shape. See Spectral-Physics-Lean issue filed 2026-10-04. -/
structure KasparovProductWitness (op : BinaryOpOnSpectra) : Prop where
  /-- Symmetry of the spectrum-side shadow (SUBSTANTIVE). -/
  symm : ∀ μ ν : Spectrum, op μ ν = op ν μ
  /-- Product-spectrum shape on squares: spec(D²) = spec(D₁²) ⊞ spec(D₂²). -/
  sq_shape : ∀ μ ν : Spectrum,
    (op μ ν).map (fun x : ℝ => x ^ 2) =
      additiveConv (μ.map (fun x : ℝ => x ^ 2)) (ν.map (fun x : ℝ => x ^ 2))

/-- Cardinality multiplicativity (former K1 statement), now derived. -/
theorem KasparovProductWitness.card_mul {op : BinaryOpOnSpectra}
    (h : KasparovProductWitness op) (μ ν : Spectrum) :
    Multiset.card (op μ ν) = Multiset.card μ * Multiset.card ν := by
  have := congrArg Multiset.card (h.sq_shape μ ν)
  simpa using this

/-! ## The three named axioms (K1, K2, K3) — DELETED (see below) -/

/-! **K1 — Mesland-Rennie 2014/2016 (Unbounded Kasparov product
cardinality)** — DELETED (2026-08-18 content repair, REPAIRED-SOUND).

Was: `∀ {op}, KasparovProductWitness op → ∀ μ ν, Multiset.card (op μ ν)
= Multiset.card μ * Multiset.card ν`, an `axiom`. Compile-verified to
derive `False` via the `zeroOp` witness (U2 in
`lean-content-audit-2026-08-18/REGISTER.md`). Its statement now
appears as an explicit hypothesis parameter (`K1`) on
`kasparov_product_satisfies_three_conditions` below, wherever the
former axiom was consumed.
-/

/-! **K2 — Rosenberg-Schochet 1987 (KK-Künneth cancellation)** —
DELETED (2026-08-18 content repair, REPAIRED-SOUND).

Was: `∀ {op}, KasparovProductWitness op → ∀ μ μ' ν, ν.NonTrivial →
op μ ν = op μ' ν → μ = μ'`, an `axiom`. Compile-verified to derive
`False` via the `zeroOp` witness (U2). Now an explicit hypothesis
parameter (`K2`) on `right_cancel_of_K2` and
`kasparov_product_satisfies_three_conditions` below.
-/

/-! **K3 — Kassel 1987/89 (Noncommutative residue multiplicativity)** —
DELETED (2026-08-18 content repair, REPAIRED-SOUND).

Was: `∀ {op}, KasparovProductWitness op → HamiltonianAdditivity op`,
an `axiom`. Compile-verified to derive `False` via the `zeroOp`
witness (U2). Now an explicit hypothesis parameter (`K3`) on
`kasparov_product_satisfies_three_conditions` and
`kasparov_product_trace_eq_additive` below.
-/

/-! ## Combining K1, K2, K3 into the narrow Path A theorem -/

/-- Right cancellation derived from K2 (REPAIRED-SOUND: now an
explicit hypothesis parameter, see K2's docstring above) and the
symmetry recorded in the Kasparov-product witness. -/
private lemma right_cancel_of_K2
    {op : BinaryOpOnSpectra} (h : KasparovProductWitness op)
    (K2 : ∀ μ μ' ν : Spectrum, ν.NonTrivial → op μ ν = op μ' ν → μ = μ') :
    ∀ μ ν ν' : Spectrum, μ.NonTrivial →
      op μ ν = op μ ν' → ν = ν' := by
  intro μ ν ν' hμ heq
  -- From symmetry of op, swap arguments
  have hsym1 : op μ ν = op ν μ := h.symm μ ν
  have hsym2 : op μ ν' = op ν' μ := h.symm μ ν'
  have h_swap : op ν μ = op ν' μ := by
    rw [← hsym1, ← hsym2]; exact heq
  exact K2 ν ν' μ hμ h_swap

/-- **Path A narrow uniqueness — OPEN (2026-09-06).** Implication
only: a `KasparovProductWitness` (now carrying `card_mul`, the
former K1) plus explicit K2/K3 hypotheses yields `ThreeConditions`.

This does **not** close Kasparov uniqueness. Mesland–Rennie,
Rosenberg–Schochet, and Kassel remain **UNFORMALISED literature**.
The caller must discharge K2 and K3; nothing in this repo does.

What this theorem does NOT say:
* It does NOT say that the composite spectrum equals `additiveConv`
  pointwise as a multiset — only that it satisfies the
  spectrum-level three-condition predicate.
* It does NOT exclude non-Kasparov binary operations from also
  satisfying the predicate.
* It does NOT assert K2/K3 for every `KasparovProductWitness`. -/
theorem kasparov_product_satisfies_three_conditions
    {op : BinaryOpOnSpectra} (h : KasparovProductWitness op)
    (K2 : ∀ μ μ' ν : Spectrum, ν.NonTrivial → op μ ν = op μ' ν → μ = μ')
    (K3 : HamiltonianAdditivity op) :
    ThreeConditions op where
  hamilton := K3
  hurwitz  :=
    ⟨⟨HurwitzLevel.sup,
       HurwitzLevel.sup_reals_left,
       HurwitzLevel.sup_reals_right⟩⟩
  faithful :=
    { card_mul    := fun μ ν => h.card_mul μ ν
      left_cancel := fun μ μ' ν hν heq =>
        K2 μ μ' ν hν heq
      right_cancel := right_cancel_of_K2 h K2 }

/-- **Corollary**: the trace channel agrees with additive convolution
— OPEN: conditional on K3 as an explicit hypothesis (formerly the
axiom `K3_kassel_residue`, deleted per U2). Kassel 1987/1989 is
UNFORMALISED literature. -/
theorem kasparov_product_trace_eq_additive
    {op : BinaryOpOnSpectra} (_h : KasparovProductWitness op)
    (K3 : HamiltonianAdditivity op)
    (μ ν : Spectrum) :
    Spectrum.trace (op μ ν) = Spectrum.trace (additiveConv μ ν) := by
  have h_op : Spectrum.trace (op μ ν) =
      (Multiset.card ν : ℝ) * Spectrum.trace μ +
        (Multiset.card μ : ℝ) * Spectrum.trace ν :=
    K3 μ ν
  rw [h_op, trace_additiveConv]

/-! ## Sanity: the witness is non-vacuous, excludes `zeroOp`, and clashes with K3 -/

/-- Concrete inhabitant: nonnegative roots of the squared-spectrum convolution. -/
noncomputable def sqrtShapeOp : BinaryOpOnSpectra :=
  ⟨fun μ ν => (additiveConv (μ.map (fun x : ℝ => x ^ 2))
    (ν.map (fun x : ℝ => x ^ 2))).map Real.sqrt⟩

private lemma additiveConv_comm (μ ν : Spectrum) :
    additiveConv μ ν = additiveConv ν μ := by
  unfold additiveConv
  rw [Multiset.bind_map_comm]
  simp [add_comm]

theorem sqrtShapeOp_witness : KasparovProductWitness sqrtShapeOp where
  symm μ ν := by
    show Multiset.map Real.sqrt _ = Multiset.map Real.sqrt _
    rw [additiveConv_comm]
  sq_shape μ ν := by
    show Multiset.map _ (Multiset.map Real.sqrt _) = _
    rw [Multiset.map_map]
    have : ∀ x ∈ additiveConv (μ.map (fun x : ℝ => x ^ 2)) (ν.map (fun x : ℝ => x ^ 2)),
        ((fun x : ℝ => x ^ 2) ∘ Real.sqrt) x = x := by
      intro x hx
      simp only [additiveConv, Multiset.mem_bind, Multiset.mem_map] at hx
      obtain ⟨_, ⟨a, _, rfl⟩, _, ⟨b, _, rfl⟩, rfl⟩ := hx
      simp only [Function.comp]
      exact Real.sq_sqrt (by positivity)
    rw [Multiset.map_congr rfl this, Multiset.map_id']

/-- The old `zeroOp` witness is still excluded. -/
theorem zeroOp_not_witness :
    ¬ KasparovProductWitness (⟨fun _ _ => (0 : Spectrum)⟩ : BinaryOpOnSpectra) := by
  intro h
  have := h.card_mul ({0} : Multiset ℝ) ({0} : Multiset ℝ)
  simp at this

/-- **Honest negative (T1)**: the witness and K3 are jointly inconsistent
(μ = {3}, ν = {4}: |op| = 5 by `sq_shape`, but K3 forces trace 7).
Hence `kasparov_product_satisfies_three_conditions` is vacuously true. -/
theorem kasparov_witness_K3_inconsistent {op : BinaryOpOnSpectra}
    (h : KasparovProductWitness op) (K3 : HamiltonianAdditivity op) : False := by
  have hc : Multiset.card (op {3} {4}) = 1 := by
    simpa using h.card_mul ({3} : Multiset ℝ) ({4} : Multiset ℝ)
  obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp hc
  have hsq := h.sq_shape ({3} : Multiset ℝ) ({4} : Multiset ℝ)
  have ht := K3 ({3} : Multiset ℝ) ({4} : Multiset ℝ)
  rw [hx] at hsq ht
  simp [additiveConv, Spectrum.trace] at hsq ht
  nlinarith [hsq, ht]

end SpectralPhysics.CompositionUniqueness
