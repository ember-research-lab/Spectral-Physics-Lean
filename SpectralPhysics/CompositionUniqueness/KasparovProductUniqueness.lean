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

## Status: honest scaffold, NOT a full formalisation of KK-theory

Mathlib has no unbounded KK-theory and no spectral-triple
infrastructure as of 2026.  What we do here is:

1. Define a witness predicate `KasparovProductWitness` recording
   the assumption "this binary operation on spectra is the
   spectrum-side shadow of an unbounded Kasparov product in the
   sense of Mesland-Rennie".

2. State three named axioms K1, K2, K3, each cited to a specific
   paper from the published literature.

3. Combine them to obtain: any binary operation carrying a
   `KasparovProductWitness` satisfies the spectrum-level
   three-condition predicate.

The honest scope is: *"Conditional on Mesland-Rennie 2013 + RS 1987
+ Kassel 1986 being correctly transcribed into spectrum-level
shadows (K1, K2, K3), every Kasparov-product operation satisfies
the three conditions."*

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

## REPAIRED-SOUND (2026-08-18 content repair) — module is now CONJECTURAL

The three named axioms K1/K2/K3 below **used to be Lean `axiom`s**.
The 2026-08-18 content audit (`lean-content-audit-2026-08-18/REGISTER.md`
U2) compile-verified that each derives `False` independently from the
`zeroOp : BinaryOpOnSpectra := ⟨fun _ _ => (0 : Spectrum)⟩` witness,
because `KasparovProductWitness.is_kk_product` is `: True` and so
places no real constraint beyond `symm` (which `zeroOp` trivially
satisfies) — see the `is_kk_product` docstring's own "AUDIT-FLAGGED"
note above, and `lean-content-audit-2026-08-18/K1Unsound.lean`
(positive control, recompiled clean before this repair).

**Repair**: K1, K2, K3 are **deleted as axioms**. This module is
**CONJECTURAL**: `kasparov_product_satisfies_three_conditions` and
`kasparov_product_trace_eq_additive` now take the former axiom
statements as **explicit hypothesis parameters** (REPAIRED-SOUND:
axiom → hypothesis) rather than deriving them from a citation-named
axiom. No sound general replacement for K1/K2/K3 is supplied here —
that would require either fixing `is_kk_product` to a real
KK-equivalence predicate (out of scope: inventing that predicate is
new math, not a content repair) or discharging the hypotheses at each
call site with a genuine witness. `open:kasparov-uniqueness` in the
trunk remains open, unchanged by this repair.

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
binary operation `op` on spectra is the spectrum-side shadow of an
unbounded Kasparov product in the Mesland-Rennie sense.

Recorded:

* `symm` — the underlying multiset is symmetric in the two
  factors (the grading γ does not change the multiset of
  eigenvalues, only their parity-pairing). **SUBSTANTIVE**.
* `is_kk_product` — abstract marker that the operation represents
  the KK-equivalence class of the exterior product. **AUDIT-FLAGGED
  (2026-05) — currently `: True`, carries no KK-theoretic content**.

**Audit warning (2026-05 cheating-pattern remediation)**: the
`is_kk_product : True` field is a PREDICATE-SHELL — `True` is
trivially provable. Theorems requiring `KasparovProductWitness op`
EFFECTIVELY only require `op` to be commutative (via the substantive
`symm` field); the "KK-product class" content is decorative.

The Mesland-Rennie 2014/2016 + Rosenberg-Schochet 1987 + Kassel 1986
literature content (the three "K1/K2/K3" axioms below) is captured at
the spectrum-shadow level via the substantive `symm` field and the
specific ∀-quantified axiom statements. To make the structure fully
faithful to KK-theory, replace `is_kk_product` with an actual
constraint (e.g., the spectrum-shadow analog of the KK-equivalence
relation). Keeping the trivial field for now to preserve downstream
type-checking; the audit note here surfaces the gap. -/
structure KasparovProductWitness (op : BinaryOpOnSpectra) : Prop where
  /-- Symmetry of the spectrum-side shadow (SUBSTANTIVE). -/
  symm : ∀ μ ν : Spectrum, op μ ν = op ν μ
  /-- **VACUOUS marker** (`: True`) — does not carry KK-product content.
      See structure docstring for audit note. -/
  is_kk_product : True

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

/-- **Path A narrow uniqueness (the headline of this file)** —
CONJECTURAL (REPAIRED-SOUND, 2026-08-18): within the category of
Kasparov-product spectral operations, the spectrum-level
three-condition predicate is necessarily satisfied, GIVEN that `op`
also satisfies the K1/K2/K3 conditions as explicit hypotheses (the
former axioms of the same names, deleted because they derive `False`
via the `zeroOp` witness — see U2 in
`lean-content-audit-2026-08-18/REGISTER.md`).

What this theorem does NOT say:
* It does NOT say that the composite spectrum equals `additiveConv`
  pointwise as a multiset — only that it satisfies the
  spectrum-level three-condition predicate.
* It does NOT exclude non-Kasparov binary operations from also
  satisfying the predicate.
* It no longer says K1/K2/K3 hold for *every* `KasparovProductWitness`
  — that was the unsound claim. They are now hypotheses the caller
  must separately discharge for their specific `op`. -/
theorem kasparov_product_satisfies_three_conditions
    {op : BinaryOpOnSpectra} (h : KasparovProductWitness op)
    (K1 : ∀ μ ν : Spectrum, Multiset.card (op μ ν) = Multiset.card μ * Multiset.card ν)
    (K2 : ∀ μ μ' ν : Spectrum, ν.NonTrivial → op μ ν = op μ' ν → μ = μ')
    (K3 : HamiltonianAdditivity op) :
    ThreeConditions op where
  hamilton := K3
  hurwitz  :=
    ⟨⟨HurwitzLevel.sup,
       HurwitzLevel.sup_reals_left,
       HurwitzLevel.sup_reals_right⟩⟩
  faithful :=
    { card_mul    := fun μ ν => K1 μ ν
      left_cancel := fun μ μ' ν hν heq =>
        K2 μ μ' ν hν heq
      right_cancel := right_cancel_of_K2 h K2 }

/-- **Corollary**: the trace channel of any Kasparov-product
spectral operation agrees with that of additive convolution —
CONJECTURAL (REPAIRED-SOUND): conditional on K3 as an explicit
hypothesis (formerly the axiom `K3_kassel_residue`, deleted per U2). -/
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
