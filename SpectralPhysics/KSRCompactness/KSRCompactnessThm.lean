/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.KSRCompactness.RellichKondrachov

/-!
# Compactness of `𝒦_SR` (conditional headline theorem)

This file proves the v0.9.2 deferred item G.2 (v0.9 lines 16759 and
11082(a)) as a **conditional Lean theorem**:

> Given the Rellich–Kondrachov named axiom and the eigenvalue-decay
> hypothesis on `𝒦_SR`, every bounded Sobolev-`s` sublevel set
> (`s > 1`, fixed bound `C > 0`) is compact in the trace-norm
> topology.

The conditional structure follows the discipline of
`compute/composition-uniqueness` Scope 3 (Kasparov-narrow): the
named axiom from the classical functional-analysis literature is the
forward direction; the headline theorem **derives** the `𝒦_SR`
compactness claim from it.

## The conditional chain

```
SobolevGrowth T s with s > 1            ──┐
∀ T ∈ KSR, SobolevGrowth T s            ──┤   (predicate hypothesis)
∃ C > 0, ∀ T, T ∈ KSRSobolev s C        ──┤
        + `rellich_kondrachov_trace_class`  → IsCompact `KSRSobolev s C`
```

So the **eigenvalue-decay hypothesis** is the predicate carrier; the
axiom is the named external fact; the conclusion is compactness of
the bounded sublevel set.

This is the "Tier 2 conditional" form anticipated in the v0.9.2
deferred document (`v092_deferred.md` §G.2, line 54): "Likely Tier 2
conditional on a Mathlib compactness lemma (Rellich–Kondrachov for
trace-class operators with controlled spectral density)."

## What is *not* claimed

* We do NOT claim `IsCompact (Set.univ : Set KSR)`.  The full
  `𝒦_SR` (Schatten-1 ideal) is **not** compact; only bounded
  Sobolev sublevel sets are.
* We do NOT discharge the self-reference invariance condition
  (`KSR.srInvariant`); that remains the open content of v0.9 line
  11079 `rem:field-eq-open(a)`.
* We do NOT claim compactness for trace-class decay rates `s ≤ 1`.

## References

* v0.9 line 16759: the `𝒦_SR` compactness need.
* v0.9 line 11082(a): "Compactness of `𝒦_SR` in the relevant
  Sobolev-type topology" — Expected positive; not written.
* `v092_deferred.md` §G.2 (line 54): the deferred-item brief.
* Rellich 1930; Kondrachov 1945; Simon 2005 *Trace Ideals*.
-/

noncomputable section

open Set

namespace SpectralPhysics.KSRCompactness

/-! ## The headline conditional theorem -/

/-- **Theorem (CONDITIONAL on `rellich_kondrachov_trace_class`).**

For trace-class decay rate `s > 1` and bound `C > 0`, the eigenvalue-
shadow Sobolev sublevel set `KSRSobolev s C` is compact.

This is a direct restatement of the named axiom — its purpose is to
expose the conditional structure: the theorem name reads as
`ksr_compact`, the dependency on the named axiom is visible to
`#print axioms`, and the hypothesis `s > 1` is *explicit*. -/
theorem ksr_compact (s C : ℝ) (h_decay : 1 < s) (h_bound : 0 < C) :
    IsCompact (KSRSobolev s C) :=
  rellich_kondrachov_trace_class s C h_decay h_bound

/-- **Corollary**: if every element of a subset `S ⊆ KSR` admits the
same Sobolev-`s` bound with shared rate constant `C > 0` (i.e.
`S ⊆ KSRSobolev s C`), then `S` is contained in a compact set.

This is the working form of the compactness theorem: a *uniform*
Sobolev bound on a family is enough to make the family precompact. -/
theorem ksr_subset_compact
    (s C : ℝ) (h_decay : 1 < s) (h_bound : 0 < C)
    (S : Set KSR) (h_uniform : S ⊆ KSRSobolev s C) :
    ∃ K : Set KSR, IsCompact K ∧ S ⊆ K :=
  ⟨KSRSobolev s C, ksr_compact s C h_decay h_bound, h_uniform⟩

/-- **Compactness preservation under intersection**: the intersection
of a Sobolev sublevel set with any closed subset of `KSR` is again
compact.  (Useful for adding extra constraints such as the
self-reference invariance, once that condition is formalised.) -/
theorem ksr_compact_inter_closed
    (s C : ℝ) (h_decay : 1 < s) (h_bound : 0 < C)
    (F : Set KSR) (hF : IsClosed F) :
    IsCompact (KSRSobolev s C ∩ F) :=
  (ksr_compact s C h_decay h_bound).inter_right hF

/-! ## The self-reference invariance overlay (Prop, NOT discharged)

We do not formalise the self-reference invariance condition itself;
v0.9 line 11079 records this as open.  But we can describe the
**conditional** compactness statement: if the SR-invariant subset
of `KSRSobolev s C` is closed, it is compact.

The closedness hypothesis is the additional content — we declare
it as a Prop hypothesis, mirroring the discipline of
`OP3/SCSEClosureSystem.lean`. -/

/-- The subset of `KSR` whose self-reference invariance condition
(`KSR.srInvariant`) holds. -/
def KSRInvariant : Set KSR := { T | T.srInvariant }

/-- **Prop hypothesis (open content, v0.9 line 11079)**: the SR-invariant
subset of `KSR` is closed in the carrier topology.

This is the v0.9.2 deferred-item analogue of the self-reference
invariance being a *closed* condition (a structurally weak version
of what one would expect for an "invariance under group action"
type condition). -/
def SRInvariantIsClosed : Prop := IsClosed KSRInvariant

/-- **Conditional theorem**: assuming `SRInvariantIsClosed`, the
SR-invariant Sobolev sublevel set is compact. -/
theorem ksr_invariant_sobolev_compact
    (s C : ℝ) (h_decay : 1 < s) (h_bound : 0 < C)
    (h_inv_closed : SRInvariantIsClosed) :
    IsCompact (KSRSobolev s C ∩ KSRInvariant) :=
  ksr_compact_inter_closed s C h_decay h_bound KSRInvariant h_inv_closed

/-! ## The full Sobolev class — non-compact (consistency check)

We **do not** assert compactness of the full Sobolev-`s` class
`{ T | SobolevGrowth T s }`; it is a union of compact sets over
`C ∈ (0, ∞)`, and such unions are typically not compact (in
particular not closed in standard Banach-space topologies).

This consistency check is recorded as a Prop with no theorem
attached; it documents what is **not** proved here, which is part
of the audit discipline. -/

/-- **Prop (record of non-compactness)**: the full Sobolev-`s`
class — the union over all `C > 0` of the bounded sublevel sets —
is generally **not** compact.  This Prop is stated for documentation
only; it is not proved here. -/
def FullSobolevClassNotCompact (s : ℝ) : Prop :=
  ¬ IsCompact { T : KSR | SobolevGrowth T s }

end SpectralPhysics.KSRCompactness

end
