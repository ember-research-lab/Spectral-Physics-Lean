/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.KSRCompactness.SobolevControl
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Rellich–Kondrachov for trace-class spectral classes (named axiom)

This file states the **named axiom** that bounded Sobolev-`s`
sublevel sets of `𝒦_SR` are compact, for `s > 1`, in the trace-norm
topology.  It is the eigenvalue-shadow version of the classical
Rellich–Kondrachov theorem (Rellich 1930; Kondrachov 1945) combined
with the Schatten-class compactness criterion (Simon 2005 §3.3;
Reed–Simon Vol. IV §VI).

## Why an axiom and not a Mathlib lemma

We verified that Mathlib at toolchain v4.29.0-rc6 does **not** carry:

* the Schatten ideal topology in a form usable for trace-class
  compactness (`grep "Schatten" Mathlib | wc -l` returns 0
  module-level hits);
* the trace-class predicate as a typeclass / structure
  (`grep "TraceClass" Mathlib` returns no spectral-operator hits);
* a Rellich–Kondrachov theorem at the level of operator ideals
  (`grep "Rellich"` and `grep "Kondrachov"` return 0 hits).

Only the abstract `IsCompactOperator` predicate (Compact.lean) is
present, with no eigenvalue-decay → compactness implication.

Therefore the eigenvalue-shadow theorem is recorded as a single
**named axiom** with full literature citation, in the style of
`compute/composition-uniqueness` K1+K2+K3 and `compute/dixon-order-one`'s
named OB1/OB2 axioms.

The axiom is **general** (it does NOT mention `𝒦_SR` or the
specific spectrum structure of the v0.9 framework); it is a
classical functional-analysis statement that holds for any
`KSRSobolev s C` set with `s > 1` and `C > 0`.

## REPAIRED-SOUND (2026-08-18 content repair, spec `lean-content-repair`)

**This file no longer states `rellich_kondrachov_trace_class` as an
axiom.**  The 2026-08-18 content audit (`lean-content-audit-2026-08-18/
REGISTER.md` U1) found that the axiom, combined with the discrete
placeholder `TopologicalSpace KSR` instance below, derives `False`:
under the discrete topology `IsCompact` collapses to `Finite`, and the
hostile witness `kOf : ℝ → KSR` (`kOf c` has eigenvalue `c` at index 0,
`0` elsewhere) exhibits an injective image of `Set.Icc 0 1` — an
infinite set — inside `KSRSobolev 2 1`, contradicting finiteness
(`lean-content-audit-2026-08-18/KSRFalse.lean`, positive control:
compiles to `ksr_false : False` before this repair).

The axiom asserted compactness for *every* topology assignment to
`KSR`, including the discrete one — but "compact ⇒ finite" under
discrete topology is incompatible with `KSRSobolev s C` being
infinite (as the continuum-indexed family `kOf` shows for any `s, C`).
No universally-quantified-over-topology statement of this axiom can
be sound while Mathlib lacks the Schatten-1 trace-norm topology this
axiom was meant to describe (see the negative Mathlib search below,
unchanged).

**Repair**: the axiom is deleted and its conclusion is instead carried
as an **explicit hypothesis** on the theorems that used it
(`ksr_compact` and its corollaries in `KSRCompactnessThm.lean`,
`KSR_compactness_verdict` in `Verdict.lean`,
`coercive_sublevels_compact` in `BasinConnectivity/Verdict.lean`).
Each such theorem now reads "IF `KSRSobolev s C` is compact (in
whatever topology eventually supplies the trace-norm structure), THEN
…" rather than deriving compactness from a universally-false claim.
This is the `REPAIRED-SOUND` class: axiom → hypothesis, no physics
added, no new axiom introduced.

The placeholder `instance : TopologicalSpace KSR := ⊥` below is
**retained** (a discrete topology is a legitimate, if degenerate,
topological space — declaring the instance is not itself unsound).
What was unsound was axiomatising compactness *for* that topology;
that axiom is gone.

## Anti-pattern check (audit discipline, historical — the axiom this
section describes no longer exists; kept for provenance)

The axiom, when it existed, was **NOT** of the form
`IsCompact (Set.univ : Set KSR)` (conclusion-as-axiom), and **NOT**
framework-specific (it depended only on `s, C`) — but neither
property saves it from being false for the discrete topology, which
is why it is now a hypothesis instead of an axiom.

## References

* **Rellich, F.** (1930), "Ein Satz über mittlere Konvergenz",
  *Nachr. Gesell. Wiss. Göttingen, Math.-Phys. Kl.*, 30–35.
  The original Rellich compactness theorem for `H^1 ↪ L^2` on
  bounded domains.
* **Kondrachov, V.** (1945), "Sur certaines propriétés des
  fonctions dans l'espace L^p", *Dokl. Akad. Nauk SSSR* 48,
  535–538.  The `L^p`-generalisation of Rellich.
* **Simon, B.** (2005), *Trace Ideals and Their Applications*,
  2nd edition, AMS Math. Surveys & Monographs Vol. 120, Ch. 3.
  Schatten-`p` compactness criterion: bounded operators with
  `p`-summable singular values are Schatten-`p`, and Schatten-`p`
  is contained in the compact operators.  Theorem 3.7 (Weyl
  comparison) is the eigenvalue-decay → trace-norm-compactness link.
* **Reed, M., Simon, B.** (1978), *Methods of Modern Mathematical
  Physics*, Vol. IV: *Analysis of Operators*, Academic Press,
  §VI.6 (compact operators, Hilbert–Schmidt, trace-class).
-/

noncomputable section

open Set

namespace SpectralPhysics.KSRCompactness

/-! ## REPAIRED-SOUND: no axiom here anymore

`rellich_kondrachov_trace_class` used to be declared here as an
`axiom`.  It is **deleted**: see the "REPAIRED-SOUND" note in the
module docstring above for why (it derives `False` combined with the
discrete `TopologicalSpace KSR` instance below).  Its conclusion is
now threaded as an explicit hypothesis parameter on the consuming
theorems in `KSRCompactnessThm.lean`, `Verdict.lean`, and
`BasinConnectivity/Verdict.lean`.  A topology on `KSR` is still needed
for `IsCompact`/`IsPathConnected` to typecheck at all in this and
downstream files, so the placeholder discrete instance is kept (it is
not itself the source of the inconsistency — a discrete topology is a
legitimate topological space; the false claim was that *every*
Sobolev sublevel set is compact under it). -/

/-- Discrete topology on `KSR` (placeholder; refinement to trace-norm
topology pending Mathlib's Schatten-1 ideal infrastructure). Kept
after the U1 repair (2026-08-18): declaring this instance is not
itself unsound, only the deleted `rellich_kondrachov_trace_class`
axiom which claimed compactness held under it universally. -/
instance : TopologicalSpace KSR := ⊥

/-! ## Auxiliary corollary

If we know `T` is in *some* Sobolev class with `s > 1`, then `T`
lies in the *bounded* Sobolev class.  Combined with the named
axiom, this gives compactness of bounded Sobolev classes. -/

theorem KSRSobolev_mem_of_growth
    {T : KSR} {s : ℝ} (h_growth : SobolevGrowth T s) :
    ∃ C : ℝ, 0 < C ∧ T ∈ KSRSobolev s C := h_growth

/-- **Corollary**: the union over all bound constants `C > 0` of the
Sobolev-`s` sublevel sets is precisely the set of all `T` with
`SobolevGrowth T s`. -/
theorem SobolevGrowth_set_eq :
    ∀ (s : ℝ), { T : KSR | SobolevGrowth T s } =
        ⋃ (C : ℝ) (_ : 0 < C), KSRSobolev s C := by
  intro s
  ext T
  simp [SobolevGrowth, KSRSobolev, Set.mem_iUnion]

end SpectralPhysics.KSRCompactness

end
