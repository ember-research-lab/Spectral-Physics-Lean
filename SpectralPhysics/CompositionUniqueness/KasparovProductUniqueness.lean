/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.CompositionUniqueness.HypothesisSet
import SpectralPhysics.CompositionUniqueness.AdditiveSatisfies

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
   pass replaces the remaining `is_kk_product : True` shell by
   the weakest field that excludes that witness (`card_mul`).

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

**2026-09-06 remaining**: `is_kk_product : True` still admitted
`zeroOp`. Replaced by `card_mul` (cardinality multiplicativity —
the former K1 statement). FLAG for Aaron: weakest hypothesis that
excludes the zero witness; not a formalisation of Mesland–Rennie.
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
unbounded Kasparov product.

Recorded:

* `symm` — the underlying multiset is symmetric in the two
  factors. **SUBSTANTIVE**.
* `card_mul` — cardinality of the composite spectrum equals the
  product of the factor cardinalities (former K1 statement).
  **SUBSTANTIVE**; excludes the `zeroOp` witness of U2.

Mesland–Rennie 2014/2016 (unbounded Kasparov product),
Rosenberg–Schochet 1987 (KK-Künneth), and Kassel 1987/1989
(noncommutative residue) remain **UNFORMALISED literature**. This
structure is not a KK-equivalence predicate.

FLAG for Aaron (2026-09-06): `card_mul` is the weakest field that
excludes `zeroOp := ⟨fun _ _ => (0 : Spectrum)⟩`. A real KK-class
constraint is not supplied. -/
structure KasparovProductWitness (op : BinaryOpOnSpectra) : Prop where
  /-- Symmetry of the spectrum-side shadow (SUBSTANTIVE). -/
  symm : ∀ μ ν : Spectrum, op μ ν = op ν μ
  /-- Cardinality multiplicativity (former K1; weakest zeroOp-excluding field). -/
  card_mul : ∀ μ ν : Spectrum,
    Multiset.card (op μ ν) = Multiset.card μ * Multiset.card ν

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

end SpectralPhysics.CompositionUniqueness
