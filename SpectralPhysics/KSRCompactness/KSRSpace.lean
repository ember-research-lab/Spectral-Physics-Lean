/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# `𝒦_SR` — the space of self-referential Hermitian kernels

This file gives the bare data carrier for `𝒦_SR`, the v0.9 §47 / line
11082(a) space of Hermitian trace-class kernels with a self-reference
invariance condition.

The full operator-theoretic content of `𝒦_SR` lives in functional
analysis (Hilbert–Schmidt → trace-class, Schatten norms, Hermitian
projection of compact operators).  Mathlib at toolchain v4.29.0-rc6
does **not** currently provide the `Schatten 1` ideal topology, the
trace-class predicate, or the Hermitian projection of compact
operators in a form usable here (we verified this by searching
`Mathlib/Analysis/Normed/Operator/Compact.lean` and the
`InnerProductSpace/Spectrum.lean` modules — only the abstract
`IsCompactOperator` predicate and finite-dimensional traces are
present).

Therefore we encode `𝒦_SR` at the **eigenvalue-list** level:

* A `KSR` is a sequence `lam : ℕ → ℝ` of real eigenvalues (Hermitian),
  packaged with a positive trace-norm `Σ |λ_k|` and a self-reference
  invariance Prop predicate.

This is the natural "spectral shadow" of the full operator-level
definition: a Hermitian trace-class operator on a separable Hilbert
space is determined (up to unitary equivalence) by its eigenvalue
sequence, and the trace-norm topology on the operator space pulls
back to the `ℓ¹` topology on the eigenvalue sequence.

The self-reference predicate `IsSelfReferential` is carried abstractly
as a `Prop`.  Formalising the full self-reference condition
(`K(x,y) = ⟨Φ(x), Φ(y)⟩` for some embedding `Φ : X → H` of states
into a self-modelling Hilbert space) is itself an open problem —
v0.9 line 11079 (`rem:field-eq-open(a)`) — and we deliberately
do **NOT** discharge it here.  It enters downstream theorems as a
hypothesis, not as a theorem.

## v0.9 line correspondence

* line 16759: the `𝒦_SR` Sobolev-compactness expectation.
* line 11082(a): "Compactness of `𝒦_SR` in the relevant Sobolev-type
  topology" — Expected positive; not written.
* line 11079 `rem:field-eq-open`: parent remark, three sub-items.

## References

* Reed–Simon, *Methods of Modern Mathematical Physics*, Vol. I §VI.6
  (compact / trace-class / Hilbert-Schmidt operators).
* Simon, B., *Trace Ideals and Their Applications* (2nd ed., AMS
  Math. Surveys 120, 2005), Ch. 1–3.
* v0.9 §47 (algebra-to-geometry transition; the `𝒦_SR` basin
  argument that motivates the compactness need).
-/

noncomputable section

open Classical

namespace SpectralPhysics.KSRCompactness

/-! ## Eigenvalue-level data carrier for Hermitian trace-class operators

A `KSR` is a sequence of real eigenvalues with controlled tail.  The
real-valuedness is the spectral shadow of Hermiticity; the `ℓ¹`
summability of `|λ_k|` is the spectral shadow of trace-class.

Self-reference invariance is carried as a `Prop` — opaque content,
mirrored from the v0.9 line 11079 open status. -/

/-- A **self-referential Hermitian kernel (eigenvalue shadow)** is a
sequence of real eigenvalues `lam : ℕ → ℝ` whose absolute values are
summable, packaged with a `Prop` placeholder recording the
self-reference invariance condition.

The `ℓ¹` summability encodes trace-class (Schatten-1) membership at
the eigenvalue level; the Prop predicate `srInvariant` is the
opaque carrier for the self-reference condition flagged in
`rem:field-eq-open(a)` (v0.9 line 11079) as itself open. -/
structure KSR where
  /-- Eigenvalue sequence (Hermitian ⇒ real). -/
  lam : ℕ → ℝ
  /-- Summability of absolute values (trace-class / Schatten-1
  at the spectral level). -/
  trace_class : Summable (fun n => |lam n|)
  /-- The self-reference invariance condition, carried as an
  opaque `Prop`.  v0.9 line 11079 flags this as open. -/
  srInvariant : Prop

/-- The trace norm `‖T‖_1 = Σ_n |λ_n|`. -/
def KSR.traceNorm (T : KSR) : ℝ := ∑' n, |T.lam n|

theorem KSR.traceNorm_nonneg (T : KSR) : 0 ≤ T.traceNorm := by
  unfold KSR.traceNorm
  exact tsum_nonneg (fun _ => abs_nonneg _)

/-- The zero kernel: all eigenvalues vanish, trivially trace-class,
self-reference predicate is `True`. -/
def KSR.zero : KSR where
  lam := fun _ => 0
  trace_class := by
    simp
  srInvariant := True

theorem KSR.zero_traceNorm : KSR.zero.traceNorm = 0 := by
  unfold KSR.traceNorm KSR.zero
  simp

/-! ## The bounded-trace-norm sublevel set

The natural ambient set for trace-ideal compactness statements is a
*bounded* trace-norm ball: `{ T : KSR | ‖T‖_1 ≤ M }`.  Unbounded
sets of trace-class operators are never compact (the trace norm is
unbounded on any non-trivial direction), so the headline theorem
must be stated for bounded sublevel sets.

This matches Simon 2005 §1.4: the trace ideal `S_1` is a Banach
space, *bounded* subsets satisfying eigenvalue-decay conditions are
relatively compact in trace norm. -/

/-- The trace-norm ball of radius `M` in `𝒦_SR`. -/
def KSRBall (M : ℝ) : Set KSR :=
  { T | T.traceNorm ≤ M }

theorem KSRBall_subset_of_le {M M' : ℝ} (h : M ≤ M') :
    KSRBall M ⊆ KSRBall M' := by
  intro T hT
  unfold KSRBall at *
  exact le_trans hT h

theorem KSR_zero_mem_KSRBall {M : ℝ} (hM : 0 ≤ M) :
    KSR.zero ∈ KSRBall M := by
  show KSR.zero.traceNorm ≤ M
  rw [KSR.zero_traceNorm]
  exact hM

end SpectralPhysics.KSRCompactness

end
