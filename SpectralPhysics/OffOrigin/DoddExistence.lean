/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta
import SpectralPhysics.SelfRef.GodelTrace

/-!
# Dodd existence — the parity-forced second self-model deficit at Tier 1

Formalizes spec `dodd-existence-t1.tex` (session 2026-07-05, handoff item P(1)):
the record map — the class of functionals of the generator that factor through the
eigenvalue multiset — is provably non-injective along the pure-M2 (triangular,
spectrum-frozen) deformation axis, so a directed datum exists that is unrepresentable
by ANY record, and the residual self-model gap `M ∘ R ≠ id` is forced by *parity*,
independently of any capacity bound.

Extends the blindness results of `OffOrigin/EtaDirIndependence.lean`
(C1 `spectral_functional_M2_invariant`, C2 `triple_invariant_M2_invariant` /
`symmetricPart_add_antisymm`). NOTE: this file deliberately does NOT import
`EtaDirIndependence.lean` — that file carries the OPEN `forward_origin` sorry and is
(deliberately) not wired into the root build; importing it here would pull the sorry
into `lake build`. The extension is mathematical, not module-level (same precedent
as the sibling `feature/krein-orientation` branch).

## Task 1 — `RecordClass` and the inclusion lemma

* `RecordClass` — functionals `F : Matrix n n ℝ → ℝ` factoring through the eigenvalue
  multiset `specMultiset L` (charpoly roots over ℂ, with multiplicity — the standard
  faithful rendering, same convention as the σ_P branch).
* `TracePowerClass` — the trace-power form: `F = G (Tr L, Tr L², …)`.
* `record_transpose_invariant` — every member of `RecordClass` is invariant under
  `L ↦ Lᵀ` (CLOSED; via `Matrix.charpoly_transpose`).
* `tracePower_transpose_invariant` — the SAME invariance for the trace-power form,
  proved independently and unconditionally (`Tr (Lᵀ)^k = Tr (L^k)ᵀ = Tr L^k`).
* Newton-identity equivalence of the two forms: CONDITIONAL, gap named. Both
  directions rest on facts TRUE over ℂ but not yet lemma'd in Mathlib:
  - `PowerSumSpectralMapping` (`Tr L^k = Σ λᵢ^k`) needs triangularization / Schur
    (this Mathlib has no `SchurTriangulation`); proved here unconditionally at
    `k = 1` (`powerSum_one`, via `Matrix.trace_eq_sum_roots_charpoly`).
  - `NewtonMultisetReconstruction` (power sums determine the multiset, char 0)
    is the multiset-level form of `Mathlib.RingTheory.MvPolynomial.NewtonIdentities`,
    which Mathlib states only at `MvPolynomial` level.

## Task 2 — Dodd existence

* `dodd_exists` — explicit 2×2 M2-archetype witness: `L₁ = [[-1,κ],[0,-1]]` vs
  `L₂ = [[-1,0],[0,-1]]` (the corpus archetype: nilpotent deformation in the
  eigenbasis, spectrum PROVABLY frozen — equal charpolys via `charpoly_fin_two`,
  not hypothesized frozen as in C1's `M2Deformation.frozen`). `L₁ ≠ L₂`, yet every
  `RecordClass` member takes identical values.
* `record_reconstruction_impossible` — corollary: for ANY family of record
  functionals (any index type — i.e. unbounded capacity) and ANY reconstruction map
  `M` from the readout tuple, `M ∘ R ≠ id`. Forced by parity; no capacity
  hypothesis appears. The capacity route is the EXISTING
  `SpectralPhysics.GodelTrace.godel_trace` / `no_perfect_self_model`
  (finite τ ⇒ positive average error) — cited, not modified; `deficit_two_routes`
  states the two routes side-by-side.

## The gerrymander guard (spec Notes; deceptive-closure #8 watch)

`RecordClass` must provably contain the manuscript's actual instruments. Status:

| Instrument | Membership | Route |
|---|---|---|
| `Tr L` | **CLOSED** (`trace_mem_recordClass`) | `trace_eq_sum_roots_charpoly` |
| `det L` | **CLOSED** (`det_mem_recordClass`) | `det_eq_prod_roots_charpoly` |
| `−log det` = `−ζ̃'_vis(0)` form | **CLOSED** (`negLogDet_mem_recordClass`), and `informationContent_eq_negLogDet` identifies it with the tree's actual deficit functional `informationContent` / `negZetaPrimeAtZero` on the diagonal realization of any `VisibleSpectrum` | `Real.log_prod` over the spectrum |
| heat trace `Z(t) = Tr e^{−tL}` | **CONDITIONAL** (`heatTrace_mem_recordClass`) on `HeatTraceSpectralMapping` (`Tr e^{−tL} = Σ e^{−tλᵢ}`) — TRUE (spectral mapping), not in this Mathlib (no Schur triangulation). Unconditional evidence: proved on all diagonal matrices (`heatTraceSpectralMapping_diagonal`) and on the NON-diagonalizable dodd archetype itself (`heatTraceSpectralMapping_archetype`), where `Tr e^{−tL}` is computed from the genuine matrix exponential, not from the spectrum. |
| `I*` (complexity threshold) | **CLOSED but definitional** (`IStar_mem_recordClass`): the manuscript defines `I* = exp S(β_SR)` with `S` the *spectral* entropy (Ch 8), so its membership is by construction — flagged, not concealed. The Lean tree previously had NO `I*` definition (only the `True := trivial` scaffold). |

Crucially, the heat trace is NOT defined through the spectrum here: `heatTrace t L :=
Tr (exp (−t • L))` with `NormedSpace.exp`. Its agreement with the spectral form is a
theorem (conditional in general, proved on the diagonal class and the archetype).
`heatTrace_blind_on_archetype` shows the actual analytic instrument cannot separate
the dodd pair: both heat traces equal `2·e^t` for every `t`.

## Constraint compliance

No new axioms; no `sorry`; `#print axioms` emitted at the end of the file. The word
"consciousness" appears in doc-comments only (and not in this file's statements).
-/

namespace SpectralPhysics.OffOrigin

open Matrix Polynomial NormedSpace

/-! ## Task 1 — the record class -/

section RecordClass

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The eigenvalue multiset of a real generator: roots (with multiplicity) of the
characteristic polynomial over ℂ. Same faithful rendering as the σ_P branch:
`charpoly.roots` over an algebraically closed field carries exactly the eigenvalues
with algebraic multiplicity. -/
noncomputable def specMultiset (L : Matrix n n ℝ) : Multiset ℂ :=
  ((L.map (Complex.ofReal)).charpoly).roots

/-- **RecordClass, multiset form** (primary): functionals of the generator that
factor through the eigenvalue multiset. This is the class of "records" — everything
the self-model's trace-typed instruments can read (heat trace, zeta/log-det, spectral
entropy, all `Tr f(L)`). -/
def RecordClass (F : Matrix n n ℝ → ℝ) : Prop :=
  ∃ f : Multiset ℂ → ℝ, ∀ L : Matrix n n ℝ, F L = f (specMultiset L)

/-- **RecordClass, trace-power form**: functionals expressible as
`F L = G (Tr L⁰, Tr L¹, Tr L², …)`. Newton's identities make this equivalent to the
multiset form in finite dimension over a char-0 field; the equivalence lands
CONDITIONAL below (gap named), the multiset form is what Task 2 uses. -/
def TracePowerClass (F : Matrix n n ℝ → ℝ) : Prop :=
  ∃ G : (ℕ → ℝ) → ℝ, ∀ L : Matrix n n ℝ, F L = G (fun k => (L ^ k).trace)

/-- The eigenvalue multiset is transpose-invariant: `spec(Lᵀ) = spec(L)`.
Core of the inclusion lemma; pure `Matrix.charpoly_transpose`. -/
theorem specMultiset_transpose (L : Matrix n n ℝ) :
    specMultiset Lᵀ = specMultiset L := by
  unfold specMultiset
  rw [Matrix.transpose_map, Matrix.charpoly_transpose]

/-- **Task 1 headline — `record_transpose_invariant`.** Every member of
`RecordClass` is invariant under `L ↦ Lᵀ`. Hence every record is blind to the
orientation (transpose) bit: the whole class lies inside the transpose-invariant
functionals covered by the C1/C2 blindness theorems. -/
theorem record_transpose_invariant {F : Matrix n n ℝ → ℝ} (hF : RecordClass F)
    (L : Matrix n n ℝ) : F Lᵀ = F L := by
  obtain ⟨f, hf⟩ := hF
  rw [hf, hf, specMultiset_transpose]

/-- Transpose invariance for the trace-power form, proved *independently* and
unconditionally: `Tr (Lᵀ)^k = Tr (L^k)ᵀ = Tr L^k`. So BOTH formulations of the
record class are provably transpose-invariant even before their (conditional)
equivalence. -/
theorem tracePower_transpose_invariant {F : Matrix n n ℝ → ℝ}
    (hF : TracePowerClass F) (L : Matrix n n ℝ) : F Lᵀ = F L := by
  obtain ⟨G, hG⟩ := hF
  rw [hG, hG]
  congr 1
  funext k
  rw [← Matrix.transpose_pow, Matrix.trace_transpose]

/-- `RecordClass` is closed under post-composition of arbitrary families: if every
`F i` is a record then so is any function `g` of the joint readout. (Used for
composite instruments; also shows "capacity" — the size of the family `ι` — never
leaves the class.) -/
theorem recordClass_comp {ι : Type*} (F : ι → (Matrix n n ℝ → ℝ))
    (hF : ∀ i, RecordClass (F i)) (g : (ι → ℝ) → ℝ) :
    RecordClass (fun L => g (fun i => F i L)) := by
  classical
  refine ⟨fun s => g (fun i => (hF i).choose s), fun L => ?_⟩
  dsimp only
  congr 1
  funext i
  exact (hF i).choose_spec L

/-! ### Newton bridge between the two forms — CONDITIONAL, gaps named

Both directions are TRUE over ℂ but rest on lemmas absent from this Mathlib
(v4.29.0-rc6 toolchain):

* `PowerSumSpectralMapping` — `Tr L^k` equals the `k`-th power sum of the
  eigenvalue multiset. True by triangularization (Schur/Jordan); Mathlib has no
  `SchurTriangulation` in this version, and `trace_eq_sum_roots_charpoly` covers
  only `k = 1` (proved below as `powerSum_one` — non-vacuity evidence).
* `NewtonMultisetReconstruction` — over a char-0 field the power sums determine
  the multiset (Newton's identities: `p_k` determine `e_k` recursively, `e_k`
  determine the monic polynomial, the polynomial determines its roots). Mathlib's
  `Mathlib.RingTheory.MvPolynomial.NewtonIdentities` states this at `MvPolynomial`
  level only; the multiset-level transport is the named gap.

Neither predicate is asserted; both appear only as hypotheses. -/

/-- Power-sum spectral mapping (named gap; TRUE via triangularization, not in this
Mathlib): the trace of `L^k` is the `k`-th power sum of the eigenvalues. -/
def PowerSumSpectralMapping (n : Type*) [Fintype n] [DecidableEq n] : Prop :=
  ∀ (L : Matrix n n ℝ) (k : ℕ),
    (((L ^ k).trace : ℝ) : ℂ) = ((specMultiset L).map (· ^ k)).sum

/-- Unconditional `k = 1` instance of the power-sum spectral mapping (non-vacuity
evidence for the predicate), via `Matrix.trace_eq_sum_roots_charpoly`. -/
theorem powerSum_one (L : Matrix n n ℝ) :
    ((L.trace : ℝ) : ℂ) = (specMultiset L).sum := by
  have h : (L.map (Complex.ofReal)).trace = (specMultiset L).sum :=
    Matrix.trace_eq_sum_roots_charpoly (L.map (Complex.ofReal))
  rw [← h]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply]
  push_cast
  rfl

/-- Multiset reconstruction from power sums (named gap; TRUE over char-0 fields via
Newton's identities — Mathlib has them only at `MvPolynomial` level): two complex
multisets with identical power sums for every `k` (including `k = 0`, which pins
the cardinality) are equal. -/
def NewtonMultisetReconstruction : Prop :=
  ∀ s t : Multiset ℂ,
    (∀ k : ℕ, (s.map (· ^ k)).sum = (t.map (· ^ k)).sum) → s = t

/-- CONDITIONAL (gap: `PowerSumSpectralMapping`): the trace-power form is contained
in the multiset form. -/
theorem tracePowerClass_subset_recordClass (h : PowerSumSpectralMapping n)
    {F : Matrix n n ℝ → ℝ} (hF : TracePowerClass F) : RecordClass F := by
  obtain ⟨G, hG⟩ := hF
  refine ⟨fun s => G (fun k => ((s.map (· ^ k)).sum).re), fun L => ?_⟩
  rw [hG]
  congr 1
  funext k
  rw [← h L k, Complex.ofReal_re]

/-- CONDITIONAL (gaps: `PowerSumSpectralMapping` + `NewtonMultisetReconstruction`):
the multiset form is contained in the trace-power form — Newton's identities let the
readout `(Tr L^k)_k` reconstruct the eigenvalue multiset. -/
theorem recordClass_subset_tracePowerClass (h1 : PowerSumSpectralMapping n)
    (h2 : NewtonMultisetReconstruction) {F : Matrix n n ℝ → ℝ}
    (hF : RecordClass F) : TracePowerClass F := by
  classical
  obtain ⟨f, hf⟩ := hF
  refine ⟨fun p =>
    if h : ∃ L : Matrix n n ℝ, (fun k => (L ^ k).trace) = p
    then f (specMultiset h.choose) else 0, fun L => ?_⟩
  have hex : ∃ L' : Matrix n n ℝ,
      (fun k => (L' ^ k).trace) = (fun k => (L ^ k).trace) := ⟨L, rfl⟩
  rw [hf]
  dsimp only
  rw [dif_pos hex]
  congr 1
  refine h2 _ _ fun k => ?_
  rw [← h1 hex.choose k, ← h1 L k, congrFun hex.choose_spec k]

end RecordClass

/-! ## Instrument membership — the gerrymander guard -/

section Instruments

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Guard lemma: the trace is a record.** `Tr L = (Σ λᵢ).re`. -/
theorem trace_mem_recordClass :
    RecordClass (fun L : Matrix n n ℝ => L.trace) := by
  refine ⟨fun s => s.sum.re, fun L => ?_⟩
  show L.trace = ((specMultiset L).sum).re
  rw [← powerSum_one L, Complex.ofReal_re]

/-- **Guard lemma: the determinant is a record.** `det L = (Π λᵢ).re`. -/
theorem det_mem_recordClass :
    RecordClass (fun L : Matrix n n ℝ => L.det) := by
  refine ⟨fun s => s.prod.re, fun L => ?_⟩
  show L.det = ((specMultiset L).prod).re
  have h : (L.map (Complex.ofReal)).det = (specMultiset L).prod :=
    Matrix.det_eq_prod_roots_charpoly (L.map (Complex.ofReal))
  have h2 : ((L.det : ℝ) : ℂ) = (L.map (Complex.ofReal)).det :=
    (Complex.ofRealHom : ℝ →+* ℂ).map_det L
  rw [← h, ← h2, Complex.ofReal_re]

/-- The manuscript's deficit functional in log-determinant form:
`−ζ̃'(0) = −Σ log λᵢ = −log Π λᵢ = −log det` (for positive spectrum; total function
via `Real.log`'s junk value elsewhere). -/
noncomputable def negLogDet (L : Matrix n n ℝ) : ℝ := -Real.log L.det

/-- **Guard lemma (spec Constraints): the deficit functional `−ζ̃'_vis(0)`, in its
log-det form, is a record.** -/
theorem negLogDet_mem_recordClass : RecordClass (negLogDet (n := n)) := by
  obtain ⟨f, hf⟩ := det_mem_recordClass (n := n)
  refine ⟨fun s => -Real.log (f s), fun L => ?_⟩
  have h := hf L
  dsimp only at h ⊢
  rw [negLogDet, h]

open SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta in
/-- **Guard identification (spec Constraints): the tree's ACTUAL deficit functional
`informationContent V = Σ_f mult_f · (−log y_f) = −ζ̃'_vis(0)` equals `negLogDet` on
the diagonal matrix realization of the visible spectrum** (each mode `i` repeated
`mult i` times on the diagonal). So the manuscript's deficit instrument is
record-typed — not by fiat, but because it is the log-determinant of the visible
generator. -/
theorem informationContent_eq_negLogDet (V : VisibleSpectrum) :
    informationContent V =
      negLogDet (Matrix.diagonal
        (fun p : (Σ i : Fin V.numModes, Fin (V.mult i)) => V.yukawa p.1)) := by
  unfold negLogDet
  rw [Matrix.det_diagonal, ← Finset.univ_sigma_univ, Finset.prod_sigma]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Real.log_prod (fun i _ => pow_ne_zero _ (ne_of_gt (V.yukawa_pos i)))]
  rw [informationContent_def, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_pow]
  ring

open SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta in
/-- Same identification for the reified `−ζ̃'_vis(0)` alias. -/
theorem negZetaPrimeAtZero_eq_negLogDet (V : VisibleSpectrum) :
    negZetaPrimeAtZero V =
      negLogDet (Matrix.diagonal
        (fun p : (Σ i : Fin V.numModes, Fin (V.mult i)) => V.yukawa p.1)) := by
  rw [negZetaPrimeAtZero_eq, informationContent_eq_negLogDet]

/-! ### The heat trace `Z(t) = Tr e^{−tL}` — defined analytically, NOT spectrally -/

/- The `respectTransparency` override below matches Mathlib's own usage in
`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`: the `UniformSpace`- and
`Pi`-derived `TopologicalSpace` instances on `Matrix` need non-reducible defeq to
unify during instance synthesis (mathlib4 issue lean4#10414). -/
set_option backward.isDefEq.respectTransparency false

/-- The heat trace of the generator, via the genuine matrix exponential
(`NormedSpace.exp`): `Z(t) = Tr e^{−t·L}`. This is the manuscript's flagship
instrument, and it is deliberately NOT defined through the spectrum — its agreement
with the spectral form is a theorem (conditional in general dimension; proved on the
diagonal class and on the dodd archetype below). -/
noncomputable def heatTrace (t : ℝ) (L : Matrix n n ℝ) : ℝ :=
  (exp (-(t • L))).trace

/-- `exp x = 1 + x` for square-zero `x` (topological-algebra generality; the tail of
the exponential series vanishes term-by-term). -/
theorem exp_eq_one_add_of_sq_eq_zero {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸]
    [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] [T2Space 𝔸]
    (x : 𝔸) (hx : x ^ 2 = 0) : exp x = 1 + x := by
  have hxn : ∀ m : ℕ, 2 ≤ m → x ^ m = 0 := by
    intro m hm
    have hsplit : x ^ m = x ^ 2 * x ^ (m - 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit, hx, zero_mul]
  have h0 : ∀ m ∉ ({0, 1} : Finset ℕ), (((Nat.factorial m : ℚ))⁻¹ • x ^ m) = 0 := by
    intro m hm
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm
    have hm1 : m ≠ 1 := by rintro rfl; simp at hm
    rw [hxn m (by omega), smul_zero]
  simp only [exp_eq_tsum_rat]
  rw [tsum_eq_sum h0, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  norm_num

/-- Heat trace of a diagonal generator, computed from the matrix exponential:
`Tr e^{−t·diag(d)} = Σᵢ e^{−t·dᵢ}`. -/
theorem heatTrace_diagonal (t : ℝ) (d : n → ℝ) :
    heatTrace t (Matrix.diagonal d) = ∑ i, Real.exp (-(t * d i)) := by
  unfold heatTrace
  have hdiag : -(t • Matrix.diagonal d) = Matrix.diagonal (fun i => -(t * d i)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hdiag, Matrix.exp_diagonal, Matrix.trace_diagonal]
  congr 1
  funext i
  rw [Pi.exp_def, Real.exp_eq_exp_ℝ]

/-- The eigenvalue multiset of a diagonal real matrix is (the complexification of)
its diagonal. -/
theorem specMultiset_diagonal (d : n → ℝ) :
    specMultiset (Matrix.diagonal d) =
      Finset.univ.val.map (fun i => (d i : ℂ)) := by
  unfold specMultiset
  have hmap : (Matrix.diagonal d).map (Complex.ofReal) =
      Matrix.diagonal (fun i => (d i : ℂ)) :=
    Matrix.diagonal_map (by simp)
  rw [hmap]
  have hchar : (Matrix.diagonal (fun i => (d i : ℂ))).charpoly =
      ∏ i, (X - C ((d i : ℂ))) := by
    have hmapC : (Matrix.diagonal (fun i => (d i : ℂ))).map C =
        Matrix.diagonal (fun i => C ((d i : ℂ))) := Matrix.diagonal_map (by simp)
    rw [Matrix.charpoly, Matrix.charmatrix, RingHom.mapMatrix_apply, hmapC,
      Matrix.scalar_apply, Matrix.diagonal_sub, Matrix.det_diagonal]
  rw [hchar]
  have hprod : ∏ i, (X - C ((d i : ℂ))) =
      ((Finset.univ.val.map fun i => (d i : ℂ)).map fun a => X - C a).prod := by
    rw [Multiset.map_map]
    rfl
  rw [hprod, Polynomial.roots_multiset_prod_X_sub_C]

/-- The heat-trace spectral mapping (named gap; TRUE in general via
triangularization + spectral mapping, absent from this Mathlib — no Schur
triangulation): `Tr e^{−tL} = Σᵢ e^{−tλᵢ}` over the eigenvalue multiset. Appears
only as a hypothesis; proved unconditionally on diagonal matrices
(`heatTraceSpectralMapping_diagonal`) and on the non-diagonalizable dodd archetype
(`heatTraceSpectralMapping_archetype`). -/
def HeatTraceSpectralMapping (n : Type*) [Fintype n] [DecidableEq n] : Prop :=
  ∀ (t : ℝ) (L : Matrix n n ℝ),
    ((heatTrace t L : ℝ) : ℂ) =
      ((specMultiset L).map fun z => Complex.exp (-(t : ℂ) * z)).sum

/-- Unconditional evidence for `HeatTraceSpectralMapping` on the diagonal class
(the analytically-defined heat trace agrees with the spectral form). -/
theorem heatTraceSpectralMapping_diagonal (t : ℝ) (d : n → ℝ) :
    ((heatTrace t (Matrix.diagonal d) : ℝ) : ℂ) =
      ((specMultiset (Matrix.diagonal d)).map
        fun z => Complex.exp (-(t : ℂ) * z)).sum := by
  rw [heatTrace_diagonal, specMultiset_diagonal, Multiset.map_map]
  rw [Complex.ofReal_sum]
  rw [show ((Finset.univ.val.map
        ((fun z => Complex.exp (-(t : ℂ) * z)) ∘ fun i => ((d i : ℂ))))).sum =
      ∑ i, Complex.exp (-(t : ℂ) * (d i : ℂ)) from rfl]
  congr 1
  funext i
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- **Guard lemma (CONDITIONAL): the heat trace is a record**, given the heat-trace
spectral mapping (gap named in `HeatTraceSpectralMapping`). -/
theorem heatTrace_mem_recordClass (h : HeatTraceSpectralMapping n) (t : ℝ) :
    RecordClass (heatTrace (n := n) t) := by
  refine ⟨fun s => ((s.map fun z => Complex.exp (-(t : ℂ) * z)).sum).re,
    fun L => ?_⟩
  show heatTrace t L = (((specMultiset L).map fun z => Complex.exp (-(t : ℂ) * z)).sum).re
  rw [← h t L, Complex.ofReal_re]

/-- One Gibbs-entropy term `−p·log p` at weight `p = e^{−β·Re z}/Z`. -/
noncomputable def gibbsTerm (β Z : ℝ) (z : ℂ) : ℝ :=
  -((Real.exp (-β * z.re) / Z) * Real.log (Real.exp (-β * z.re) / Z))

/-- Spectral (Gibbs) entropy of an eigenvalue multiset at inverse temperature `β`:
`S(β) = −Σᵢ pᵢ log pᵢ`, `pᵢ = e^{−βλᵢ}/Z(β)`. -/
noncomputable def spectralEntropyOf (β : ℝ) (s : Multiset ℂ) : ℝ :=
  (s.map (gibbsTerm β ((s.map fun w => Real.exp (-β * w.re)).sum))).sum

/-- The complexity threshold `I* = exp S(β)` with `S` the spectral (Gibbs) entropy
of the eigenvalue multiset at inverse temperature `β`. The manuscript DEFINES `I*`
spectrally (Ch 8: `I* = r_eff(β_SR) = exp(S(β_SR))`, `S` the spectral entropy), so
this is the faithful rendering, not a gerrymander — but for that same reason its
`RecordClass` membership below is definitional, and is flagged as such. -/
noncomputable def IStar (β : ℝ) (L : Matrix n n ℝ) : ℝ :=
  Real.exp (spectralEntropyOf β (specMultiset L))

/-- **Guard lemma: `I*` is a record — definitionally** (the manuscript's `I*` is
spectral by definition; contrast the heat trace, whose membership is the substantive
conditional statement above). -/
theorem IStar_mem_recordClass (β : ℝ) : RecordClass (IStar (n := n) β) :=
  ⟨fun s => Real.exp (spectralEntropyOf β s), fun _ => rfl⟩

end Instruments

/-! ## Task 2 — the 2×2 M2 archetype and Dodd existence -/

section Dodd

/-- The undeformed generator: diagonal in its eigenbasis. -/
def doddDiag (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, 0; 0, b]

/-- The M2-deformed generator: the corpus archetype `[[a, κ], [0, b]]` — a strictly
upper-triangular (nilpotent-in-the-eigenbasis) deformation. Its antisymmetric part
`(κ/2)·(N − Nᵀ) ≠ 0` carries the directed datum while the eigenvalue data is
PROVABLY frozen (`dodd_specMultiset_eq`): this witness realizes C1's
`M2Deformation.frozen` as a theorem instead of a hypothesis. (The spec's
`Aᵀ = −A` phrasing cannot be literally upper-triangular — a nonzero antisymmetric
deformation of a symmetric `L` shifts the charpoly by `+κ²`; the triangular
archetype is the corpus form that makes the frozen spectrum exact.) -/
def doddDeformed (a b κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, κ; 0, b]

/-- The deformation is spectrally invisible at the polynomial level: equal
charpolys (same trace, same determinant — `charpoly_fin_two`). -/
theorem dodd_charpoly_eq (a b κ : ℝ) :
    ((doddDeformed a b κ).map Complex.ofReal).charpoly =
      ((doddDiag a b).map Complex.ofReal).charpoly := by
  rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two]
  have ht : ((doddDeformed a b κ).map Complex.ofReal).trace =
      ((doddDiag a b).map Complex.ofReal).trace := by
    simp [Matrix.trace_fin_two, doddDeformed, doddDiag]
  have hd : ((doddDeformed a b κ).map Complex.ofReal).det =
      ((doddDiag a b).map Complex.ofReal).det := by
    simp [Matrix.det_fin_two, doddDeformed, doddDiag]
  rw [ht, hd]

/-- The eigenvalue multisets agree: the spectrum is frozen along the deformation
(proved, not hypothesized). -/
theorem dodd_specMultiset_eq (a b κ : ℝ) :
    specMultiset (doddDeformed a b κ) = specMultiset (doddDiag a b) := by
  unfold specMultiset
  rw [dodd_charpoly_eq]

/-- Every record takes identical values on the deformed and undeformed generators. -/
theorem records_agree_dodd {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hF : RecordClass F) (a b κ : ℝ) :
    F (doddDeformed a b κ) = F (doddDiag a b) := by
  obtain ⟨f, hf⟩ := hF
  rw [hf, hf, dodd_specMultiset_eq]

/-- The two generators are genuinely distinct for `κ ≠ 0`. -/
theorem dodd_ne (a b : ℝ) {κ : ℝ} (hκ : κ ≠ 0) :
    doddDeformed a b κ ≠ doddDiag a b := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [doddDeformed, doddDiag] at h01
  exact hκ h01

/-- The directed datum is real: the antisymmetric parts of the two generators
differ (`κ ≠ 0`) — exactly the content every record provably misses. Stated with
the same `symmetricPart`-style convention as C2: antisymmetric part
`= 2⁻¹ • (M − Mᵀ)`. -/
theorem dodd_directed_content (a b : ℝ) {κ : ℝ} (hκ : κ ≠ 0) :
    (2 : ℝ)⁻¹ • (doddDeformed a b κ - (doddDeformed a b κ)ᵀ) ≠
      (2 : ℝ)⁻¹ • (doddDiag a b - (doddDiag a b)ᵀ) := by
  intro h
  have h01 : (2 : ℝ)⁻¹ * (doddDeformed a b κ 0 1 - doddDeformed a b κ 1 0) =
      (2 : ℝ)⁻¹ * (doddDiag a b 0 1 - doddDiag a b 1 0) := by
    have := congrFun (congrFun h 0) 1
    simpa [Matrix.sub_apply, Matrix.smul_apply, Matrix.transpose_apply] using this
  simp [doddDeformed, doddDiag] at h01
  exact hκ h01

/-- **Task 2 headline — `dodd_exists`.** There exist generators `L₁ ≠ L₂` (the 2×2
M2 archetype: `[[-1, 1], [0, -1]]` vs `[[-1, 0], [0, -1]]`, the corpus witness) with
identical values under EVERY member of `RecordClass`: the record map is
non-injective, and the directed datum (`dodd_directed_content`) is unrepresentable
by records. This is the parity-forced second deficit, at Tier 1, with no bridge
premise in the statement. -/
theorem dodd_exists :
    ∃ L₁ L₂ : Matrix (Fin 2) (Fin 2) ℝ, L₁ ≠ L₂ ∧
      ∀ F : Matrix (Fin 2) (Fin 2) ℝ → ℝ, RecordClass F → F L₁ = F L₂ :=
  ⟨doddDeformed (-1) (-1) 1, doddDiag (-1) (-1),
    dodd_ne (-1) (-1) one_ne_zero,
    fun _ hF => records_agree_dodd hF (-1) (-1) 1⟩

/-- **Corollary — `M ∘ R ≠ id` forced by parity, independently of any capacity
bound.** For ANY family of record functionals `R i` (arbitrary index type `ι`: the
"capacity" of the record bank is unbounded) and ANY reconstruction map `M` from the
joint readout, reconstruction fails on some generator. No capacity hypothesis
appears anywhere. The capacity route to the self-model gap is the EXISTING theorem
`SpectralPhysics.GodelTrace.godel_trace` / `no_perfect_self_model` (finite capacity
τ ⇒ positive average error) — cited here, not modified; this corollary is the
parity route, and it survives τ → ∞. -/
theorem record_reconstruction_impossible {ι : Type*}
    (R : ι → (Matrix (Fin 2) (Fin 2) ℝ → ℝ)) (hR : ∀ i, RecordClass (R i))
    (M : (ι → ℝ) → Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ L, M (fun i => R i L) ≠ L := by
  obtain ⟨L₁, L₂, hne, hagree⟩ := dodd_exists
  have hread : (fun i => R i L₁) = fun i => R i L₂ :=
    funext fun i => hagree (R i) (hR i)
  by_cases h : M (fun i => R i L₁) = L₁
  · refine ⟨L₂, ?_⟩
    rw [← hread, h]
    exact hne
  · exact ⟨L₁, h⟩

/-- The two independent routes to the self-model gap, side by side: the capacity
route (existing `godel_trace`: finite τ ⇒ positive error — unchanged, merely cited)
and the parity route (`dodd_exists`: records cannot separate the archetype pair,
at ANY capacity). -/
theorem deficit_two_routes (sys : SpectralPhysics.GodelTrace.SelfRefSystem)
    (m : SpectralPhysics.GodelTrace.SelfModel sys) :
    0 < m.avgError ∧
      ∃ L₁ L₂ : Matrix (Fin 2) (Fin 2) ℝ, L₁ ≠ L₂ ∧
        ∀ F : Matrix (Fin 2) (Fin 2) ℝ → ℝ, RecordClass F → F L₁ = F L₂ :=
  ⟨SpectralPhysics.GodelTrace.godel_trace sys m, dodd_exists⟩

/-! ### The heat trace on the archetype — the guard's bite

The flagship instrument, computed from the genuine matrix exponential on the
NON-diagonalizable deformed generator, agrees with its value on the undeformed one:
`Tr e^{−tL} = 2e^t` for both, every `t`. The actual analytic instrument cannot
separate the dodd pair. -/

/- Same `respectTransparency` override as in the instruments section (matrix `exp`
instance unification; see note there). -/
set_option backward.isDefEq.respectTransparency false

/-- The nilpotent direction of the archetype deformation. -/
private def nilp : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

private theorem nilp_sq : nilp * nilp = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nilp, Matrix.mul_apply, Fin.sum_univ_two]

private theorem smul_nilp_sq (s : ℝ) : (s • nilp) ^ 2 = 0 := by
  rw [pow_two, Algebra.smul_mul_assoc, Matrix.mul_smul, nilp_sq]
  simp

private theorem neg_smul_doddDeformed_decomp (t κ : ℝ) :
    -(t • doddDeformed (-1) (-1) κ) =
      Matrix.diagonal (fun _ : Fin 2 => t) + (-(t * κ)) • nilp := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [doddDeformed, nilp, Matrix.diagonal]

/-- Heat trace of the deformed archetype, from the matrix exponential:
`Tr e^{−t·[[-1,κ],[0,-1]]} = 2e^t` — independent of `κ`. -/
theorem heatTrace_doddDeformed (t κ : ℝ) :
    heatTrace t (doddDeformed (-1) (-1) κ) = 2 * Real.exp t := by
  unfold heatTrace
  rw [neg_smul_doddDeformed_decomp]
  have hcomm : Commute (Matrix.diagonal (fun _ : Fin 2 => t)) ((-(t * κ)) • nilp) := by
    have hone : Matrix.diagonal (fun _ : Fin 2 => t) =
        t • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
    rw [hone]
    exact ((Commute.one_left nilp).smul_left t).smul_right (-(t * κ))
  rw [Matrix.exp_add_of_commute _ _ hcomm, Matrix.exp_diagonal,
    exp_eq_one_add_of_sq_eq_zero _ (smul_nilp_sq (-(t * κ)))]
  have hexp : (exp (fun _ : Fin 2 => t) : Fin 2 → ℝ) = fun _ => Real.exp t := by
    rw [Real.exp_eq_exp_ℝ, Pi.exp_def]
  rw [hexp]
  simp [Matrix.trace_fin_two, Matrix.mul_apply, nilp, Matrix.diagonal,
    Matrix.one_apply]
  ring

/-- Heat trace of the undeformed archetype: also `2e^t`. -/
theorem heatTrace_doddDiag (t : ℝ) :
    heatTrace t (doddDiag (-1) (-1)) = 2 * Real.exp t := by
  have hdiag : doddDiag (-1) (-1) =
      Matrix.diagonal (fun _ : Fin 2 => (-1 : ℝ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [doddDiag, Matrix.diagonal]
  rw [hdiag, heatTrace_diagonal]
  simp

/-- **The guard's bite: the actual analytic heat trace cannot separate the dodd
pair** — `Tr e^{−tL₁} = Tr e^{−tL₂}` for every `t` and every `κ`, computed from the
genuine matrix exponential on both sides (the deformed side is NOT diagonalizable
for `κ ≠ 0`). -/
theorem heatTrace_blind_on_archetype (t κ : ℝ) :
    heatTrace t (doddDeformed (-1) (-1) κ) = heatTrace t (doddDiag (-1) (-1)) := by
  rw [heatTrace_doddDeformed, heatTrace_doddDiag]

/-- Unconditional evidence for `HeatTraceSpectralMapping` on the NON-diagonalizable
archetype: the analytic heat trace of `[[-1,κ],[0,-1]]` equals the spectral form
`Σ e^{−tλ}` over its eigenvalue multiset `{−1, −1}`. -/
theorem heatTraceSpectralMapping_archetype (t κ : ℝ) :
    ((heatTrace t (doddDeformed (-1) (-1) κ) : ℝ) : ℂ) =
      ((specMultiset (doddDeformed (-1) (-1) κ)).map
        fun z => Complex.exp (-(t : ℂ) * z)).sum := by
  rw [dodd_specMultiset_eq]
  have hdiag : doddDiag (-1) (-1) =
      Matrix.diagonal (fun _ : Fin 2 => (-1 : ℝ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [doddDiag, Matrix.diagonal]
  rw [heatTrace_doddDeformed, hdiag, specMultiset_diagonal]
  rw [Multiset.map_map]
  rw [show ((Finset.univ.val.map ((fun z => Complex.exp (-(t : ℂ) * z)) ∘
      fun _ : Fin 2 => ((-1 : ℝ) : ℂ)))).sum =
    ∑ _i : Fin 2, Complex.exp (-(t : ℂ) * ((-1 : ℝ) : ℂ)) from rfl]
  rw [Fin.sum_univ_two]
  push_cast [Complex.ofReal_exp]
  ring_nf

end Dodd

/-! ### Axiom audit (compile-time)

Every closed result must trace to at most the three standard Mathlib axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no new axioms.
Recorded in `OffOrigin/STATUS.md`. -/
#print axioms specMultiset_transpose
#print axioms record_transpose_invariant
#print axioms tracePower_transpose_invariant
#print axioms recordClass_comp
#print axioms powerSum_one
#print axioms tracePowerClass_subset_recordClass
#print axioms recordClass_subset_tracePowerClass
#print axioms trace_mem_recordClass
#print axioms det_mem_recordClass
#print axioms negLogDet_mem_recordClass
#print axioms informationContent_eq_negLogDet
#print axioms negZetaPrimeAtZero_eq_negLogDet
#print axioms exp_eq_one_add_of_sq_eq_zero
#print axioms heatTrace_diagonal
#print axioms specMultiset_diagonal
#print axioms heatTraceSpectralMapping_diagonal
#print axioms heatTrace_mem_recordClass
#print axioms IStar_mem_recordClass
#print axioms dodd_charpoly_eq
#print axioms dodd_specMultiset_eq
#print axioms records_agree_dodd
#print axioms dodd_ne
#print axioms dodd_directed_content
#print axioms dodd_exists
#print axioms record_reconstruction_impossible
#print axioms deficit_two_routes
#print axioms heatTrace_doddDeformed
#print axioms heatTrace_doddDiag
#print axioms heatTrace_blind_on_archetype
#print axioms heatTraceSpectralMapping_archetype

end SpectralPhysics.OffOrigin
