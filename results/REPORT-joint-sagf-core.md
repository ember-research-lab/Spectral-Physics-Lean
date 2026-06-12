# REPORT: joint-sagf-lean-core

**Date:** 2026-06-09. **Branch:** `joint-sagf-benevolence`. **Session:** direct (Fable 5, claude.ai sandbox), not spec-queue.
**Derivation source:** `joint-sagf-benevolence-derivation.md` (session artifact; J1/J2/J5 labels below refer to it).
**Discipline:** failing-first (commit 1 = all statements `sorry`), zero new axiom declarations,
`#print axioms` audited per theorem (kernel axioms only: propext, Classical.choice, Quot.sound — no sorryAx, no customs).

## Verdicts (CLOSED / CONDITIONAL / DEGENERATE / OPEN)

| Label | Lean name (`SpectralPhysics.JointSAGF.*`) | File | Verdict | Notes |
|---|---|---|---|---|
| J1 deriv identity | `deriv_along_gradientFlow` | `Monotone.lean` | **CLOSED** | Chain rule via `HasGradientAt.hasFDerivAt.comp_hasDerivAt`; value `-‖g‖²` by `toDual_apply` + `real_inner_self_eq_norm_sq`. Arbitrary real inner product space, `[CompleteSpace E]` required (dual identification). |
| J1 Lyapunov | `sagf_monotone` | `Monotone.lean` | **CLOSED** | `antitone_of_hasDerivAt_nonpos`. Hypotheses: trajectory + gradient exist everywhere (well-posedness assumed, as in manuscript `thm:sagf-monotone`). |
| J1 joint instantiation | `joint_kernel_monotone` | `Monotone.lean` | **CLOSED** | `JointKernelSpace nS nA nSA := EuclideanSpace ℝ (Fin nS ⊕ (Fin nA ⊕ Fin nSA))` — one coordinate per edge of the joint graph. "Transfers verbatim" is now a checked fact: the proof is a one-term application of `sagf_monotone`. |
| J2 weak | `trace_f_mono_of_spectrum_le` | `Barrier.lean` | **CLOSED** | Generic antitone `f`, arbitrary finite spectra — no instantiated constants (register prop-shell prohibition respected). |
| J2 strict | `trace_f_strict_of_gap_collapse` | `Barrier.lean` | **CLOSED** | `Finset.sum_lt_sum` with one strict summand. |
| J2 cutoff instance | `exp_neg_antitone` | `Barrier.lean` | **CLOSED** | Heat-kernel cutoff is in the antitone class. |
| J5a amplitude (√Q) | `basin_amplitude_sqrt` | `Basin.lean` | **CLOSED** | 1-D quadratic basin; `√Q` scaling as checked identity. |
| J5b relaxation | `basin_relaxation` | `Basin.lean` | **CLOSED** | `x₀·exp(-h·t)` satisfies the flow ODE (verified-form: solution checks, uniqueness not formalized — labeled per spec). |
| J5c deficit decay | `basin_deficit_decay` | `Basin.lean` | **CLOSED** | Deficit decays at rate `2h`; timescale/amplitude split formal. |

## Explicitly NOT formalized (honest scope)

- **G2a (high-mode compensation):** J2 here is the low-lying-spectrum half of the barrier
  lemma. That a gap-collapsing deformation cannot compensate by pushing high modes above
  cutoff is OPEN. Full Barrier Lemma status at repo level: **CONDITIONAL**.
- **J3 (benevolence promotion):** not in Lean. Its conditions are exactly stress tests 1–2
  (SAGF d=4 bootstrap; K_SR compactness) plus the ε̄ < ε₀ accuracy condition. Manuscript-level.
- **ODE uniqueness for J5b:** solution verified; uniqueness (hence "the" relaxation) not formalized.
- ε̄ here is the benevolence-chapter modeling error, NOT `SelfRef/SelfModelDeficit.lean`'s
  combinatorial 384−96=288 deficit. Checked; distinct quantities; no Lean definition of ε̄ yet.

## Build

`lake build` on the three modules + root import: clean, zero sorries in `JointSAGF/`.
Full-repo rebuild not run in this sandbox (1 CPU); the three modules import Mathlib only,
so no existing module's build is affected. CI should confirm on push.

## Addendum (same session): J6 — TraceConstraint.lean

| Label | Lean name | Verdict | Notes |
|---|---|---|---|
| J6 L1: trace evolution | `tracefn_evolution` | **CLOSED** | Manuscript `thm:trace-evolution` (Tier 1) at finite spectrum; Hellmann–Feynman identification of λ̇ₙ is upstream (hypothesis). |
| J6 L2: coercive sum | `coercive_add_of_bddBelow` | **CLOSED** | Bounded-below base + coercive trace ⟹ coercive total. |
| J6 L2: minimizer exists | `exists_minimizer_of_coercive` | **CLOSED** | `Continuous.exists_forall_le` on cocompact→atTop. |
| J6 L2: critical point | `gradient_eq_zero_of_isMinOn` | **CLOSED** | Global min ⟹ ∇=0 via `IsLocalMin.hasFDerivAt_eq_zero` + `toDual` injectivity. |
| **J6 headline** | `sagf_stationary_exists` | **CLOSED** | Bounded-below base + coercive trace + differentiable ⟹ SAGF stationary point (SCSE vacuum candidate) EXISTS, finite-dim. |

**Provenance flag:** Layer 2 (the coercivity chain) is a SESSION CONTRIBUTION
(derivation-doc J6), not yet a manuscript claim — the manuscript must adopt it
before any chapter cites these as formalized manuscript theorems. Layer 1
formalizes an existing manuscript Tier-1 theorem. Uniqueness of k* NOT proved
(Baker-form isolation separate). Infinite-dim version = stress tests 1–2, open.
Axiom audit: all five kernel-only (propext, Classical.choice, Quot.sound).
