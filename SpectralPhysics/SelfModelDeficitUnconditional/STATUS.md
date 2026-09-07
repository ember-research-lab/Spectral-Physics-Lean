# Self-Model Deficit Theorem — Conditional Sandwich: STATUS

**Branch**: `lean-cleanup-A-2026-09-06`
**Target**: v0.9.2 deferred item C.1.  This module does **not** close C.1.

## 2026-09-06 honesty pass (lane A)

Deleted three axioms:

* `IsPhysicalSpectrum : VisibleSpectrum → Prop` (`PhysicalSpectrum.lean`)
* `BekensteinInformationBound` (`CapacityBound.lean`)
* `NaturalityCoherence` (`NaturalityBound.lean`)

The former headline `self_model_deficit_unconditional` took
`IsPhysicalSpectrum V` and concluded `negZetaPrimeAtZero V = 288`.
The only documented model was `IsPhysicalSpectrum V := (informationContent V = 288)`,
so the theorem was a hypothesis=conclusion shell.  STATUS.md:53–57 and
README.md:84 claiming a hypothesis-free `∀ V, negZetaPrimeAtZero V = 288`
were stale (already false after the 2026-06-12 physicality guard, and
the guard itself was the shell).

**Current headline** (same as `Theorem.lean:170–176`):

```
self_model_deficit_conditional
  (V : VisibleSpectrum)
  (h_completeness : CompletenessAtLevel2 … (negZetaPrimeAtZero V))
  (h_sector : SectorFaithfulNoDeadWeight … (negZetaPrimeAtZero V)) :
  negZetaPrimeAtZero V = (288 : ℝ)
```

Manuscript `thm:ember-reconstruction` H4 treats `−ζ̃′_vis(0) = 288` as a
Tier-3 **posit**, not a derivation.  That posit is named
`CapacityPosit288` (`PhysicalSpectrum.lean`) — a `def`, not an `axiom`,
and not used as a theorem hypothesis concluding 288.

## Files

```
SelfModelDeficitUnconditional/
├── PredicateInventory.lean    — v0.9.1 predicates, still open hypotheses
├── PhysicalSpectrum.lean      — CapacityPosit288 (H4, Tier 3 posit)
├── CapacityBound.lean         — Bekenstein axiom withdrawn
├── NaturalityBound.lean       — Mac Lane axiom withdrawn
├── MellinFunctionalDet.lean   — Mellin alias (theorem, not axiom)
├── UnconditionalGoal.lean     — `_conditional` sandwich re-exports
├── Verdict.lean               — V092PartialVerdict = the sandwich
└── STATUS.md                  — this file
```

Hostile check: `test/SMDUHostile.lean` (imported from `SpectralPhysics.lean`).

## What remains open

The two named hypotheses are not discharged.  Closing them is the
operator-algebraic gap v0.9 line 8464 flags.  H4 is not derived.

## Anti-pattern check

* **Conclusion-as-axiom**: not present.  No `axiom … = 288`.
* **Opaque-predicate shell**: retired.  No `IsPhysicalSpectrum`.
* **"Unconditional" / "hypothesis-free" overclaim**: retired.  Names are
  `_conditional`.  Verdict is **PARTIAL**.

## Verdict

**PARTIAL** — 288 equality is the Level-2 sandwich, kernel axioms only.
H4 remains a Tier-3 posit.
