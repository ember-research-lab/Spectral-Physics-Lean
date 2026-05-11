/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.CompositionBroaderUniqueness.NonKasparovCandidates
import SpectralPhysics.CompositionBroaderUniqueness.TraceLevelDistinction
import SpectralPhysics.CompositionBroaderUniqueness.HigherMomentObstruction
import SpectralPhysics.CompositionBroaderUniqueness.UncountableObstruction

/-!
# CompositionBroaderUniqueness — Verdict File

This file assembles the v0.9.2 deferred-A.1 closure verdict.

## Verdict: CONDITIONAL / PARTIAL

* **CLOSED** — among the four named non-Kasparov candidates
  (free-Voiculescu `⊞`, multiplicative-free `⊠`,
  monoidal-non-Kasparov tensor cat, boxed `⊞ₐ` at the witness
  parameter `a = 1`), the three-condition predicate selects
  `additive`.  Proved Tier-1 in
  `HigherMomentObstruction.lean`, conditional only on v0.9.1's
  existing axiom set (no new axioms introduced for the named
  closure).

* **OPEN** — the *uncountable* closure (every non-Kasparov
  factorization, not just the named four) requires a
  free-probability-level theorem that is not in published form.
  Recorded as the `BroaderUniquenessAllNonKasparov` predicate in
  `UncountableObstruction.lean`, equivalent to the named
  `FreeProbResearchProgram`.

## Exact scope statement

  *For every named non-Kasparov candidate `c` in `{additive,
  freeVoiculescu, multFree, monoidalNonK, boxed-at-1}` and every
  three-condition operation `op` equal to `c`, `op = additive`.
  The uncountable closure for **all** binary operations remains
  open and is identified with the Nica–Speicher (2006) §10.5–§11
  free-probability moment-problem analogue.*

## Re-exports

The headline theorem of this module is
`broader_uniqueness_among_named_candidates`.  The honest open
predicate is `BroaderUniquenessAllNonKasparov`.

## References

See `STATUS.md` for the full accounting (Tier-1 theorems, named
axioms with citations, predicates carrying open content,
verdict).
-/

namespace SpectralPhysics.CompositionBroaderUniqueness

open SpectralPhysics.CompositionUniqueness

/-! ## Verdict at a glance -/

/-- **Verdict**: the named non-Kasparov candidates are closed at
Tier 1 under the three-condition predicate.  See file docstring
for the exact scope statement. -/
theorem verdict_named_closure
    {op : BinaryOpOnSpectra}
    (h_named : IsNamedCandidate op)
    (h_three : ThreeConditions op) :
    op = BinaryOpOnSpectra.additive :=
  broader_uniqueness_among_named_candidates h_named h_three

/-- **Verdict (trace-channel)**: even without resolving the
uncountable closure, the *trace channel* of any three-condition
operation matches additive convolution — this is the v0.9.1
unconditional Scope-2 result, re-exported here.  -/
theorem verdict_trace_channel
    (op : BinaryOpOnSpectra) (h_three : ThreeConditions op)
    (μ ν : Spectrum) :
    Spectrum.trace (op μ ν) = Spectrum.trace (additiveConv μ ν) :=
  three_conditions_force_trace_law op h_three μ ν

/-- **Verdict (open)**: the uncountable closure is the
free-probability research program; equivalent to the named
predicate `FreeProbResearchProgram`.  Not closed in this
branch. -/
theorem verdict_uncountable_open :
    BroaderUniquenessAllNonKasparov ↔ FreeProbResearchProgram :=
  v092_A1_open

end SpectralPhysics.CompositionBroaderUniqueness
