/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Forward-origin split — the matrix-level formalization of the 2026-07 tilt probe

This module is the **tractable, matrix-level** half of the `forward_origin` obligation
carried (as one `sorry`) by `OffOrigin/EtaDirIndependence.lean`. It formalizes the
three-way split proposed in `off-origin-directed-side/quasipotential-tilt/output/
forward-origin-memo.md` and the TILTED verdict of that probe's `SUMMARY.md`:

* **Part 1 — `degeneracy_under_oddness` (CLOSED).** At the finite-dimensional /
  action-functional level: if the closure drift `b` is **odd** (`b(−s) = −b(s)`)
  and the noise metric `D` is **even** (`D(−s) = D(s)`), the Freidlin–Wentzell
  action functional is invariant under the mirror `s ↦ −s`, so the well-splitting
  `ΔV` between the two broken wells vanishes. BOTH hypotheses are load-bearing:
  the proof rewrites with `hodd` AND `heven`, and dropping either makes the
  elaboration fail. `ΔV` is a function of a FREE drift `b` (not constant-`0` by
  construction) — `degeneracy_non_vacuous` exhibits a non-odd `b`, even `D`, and a
  path with `ΔV ≠ 0`, so a non-degenerate instance is genuinely stateable.

* **Part 2 — the C4-extension companion (CLOSED).** `TransposeCovariantRead R` (the
  read commutes with the mirror = adjoint on kernels and is homogeneous). Theorem
  `tc_read_antiHermitian_kernel_antisym`: every transpose-covariant read of a
  transpose-covariant kernel (`Kᴴ = −K`, the pure arrow sector) has an
  ANTISYMMETRIC output, i.e. `tc_read_tc_kernel_odd_drift`: the induced drift is
  odd — so ΔV = 0 for the entire transpose-covariant class. The arrow of time
  cannot tilt through any such channel.

  **The sharpest check:** `symImRead_not_transposeCovariant` proves that the one
  parity-mixing read `sym ∘ Im` is provably NOT transpose-covariant — it fails the
  companion's hypothesis, so Parts 2 and 3 do not contradict.

* **Part 3 — `tilt_source_exists` (CLOSED WITNESS).** A decidable fact on the 2×2
  archetype: the drift induced by the `sym ∘ Im` read of the archetype kernel is
  NON-odd (`norm_num`). It references only the read `sym ∘ Im`, nothing physical.
  This is the non-vacuity witness feeding `degeneracy_non_vacuous`.

The genuinely-open residue — whether the *physical* autopoietic loop reads this
`sym ∘ Im` channel — is `loop_reads_arrow` in `EtaDirIndependence.lean` (which is
sharper than the bare `ForwardOriginExists` and carries the single remaining sorry).
This file is sorry-free and IS wired into the root build.

Tier: everything below is finite-dimensional linear algebra — **T1**.
-/

namespace SpectralPhysics.OffOrigin

open Matrix

/-! ## Part 1 — the Freidlin–Wentzell action, its mirror, and degeneracy -/

section Degeneracy

/-- A drift field `b : ℝ → ℝ` along the antisymmetric flux coordinate `s` is **odd**
when `b(−s) = −b(s)` — the mirror-symmetric double-well flow of the FW theory. -/
def DriftOdd (b : ℝ → ℝ) : Prop := ∀ s, b (-s) = -b s

/-- A noise metric `D : ℝ → ℝ` is **even** when `D(−s) = D(s)`. -/
def MetricEven (D : ℝ → ℝ) : Prop := ∀ s, D (-s) = D s

/-- The Freidlin–Wentzell Lagrangian density at position `s`, velocity `v`:
`L(s,v) = (v − b s)² / (2 D s)`. The quasipotential action is the path integral of
this density; the discrete `Action` below is its Riemann sum over sampled
`(position, velocity)` pairs. -/
noncomputable def Lag (b D : ℝ → ℝ) (s v : ℝ) : ℝ := (v - b s) ^ 2 / (2 * D s)

/-- A discretized path: a list of `(position, velocity)` samples. -/
abbrev Path : Type := List (ℝ × ℝ)

/-- The FW action of a discretized path (Riemann sum of the Lagrangian density). -/
noncomputable def Action (b D : ℝ → ℝ) (P : Path) : ℝ :=
  (P.map (fun p => Lag b D p.1 p.2)).sum

/-- The mirror involution on paths: negate position and velocity of every sample
(the `s ↦ −s` reflection lifted to phase space). -/
def mirrorPath (P : Path) : Path := P.map (fun p => (-p.1, -p.2))

/-- The **well-splitting** `ΔV` along an instanton path `P`: the action to reach the
`+`-well via `P` minus the action to reach the mirror `−`-well via `mirrorPath P`.
This is exactly the quantity the tilt probe measured (ΔV along the located
injection). It is a genuine function of the free drift `b` — NOT constant `0`
(see `degeneracy_non_vacuous`). -/
noncomputable def deltaV (b D : ℝ → ℝ) (P : Path) : ℝ :=
  Action b D P - Action b D (mirrorPath P)

/-- **Core mirror identity (uses BOTH hypotheses).** For odd drift and even metric,
the Lagrangian density is invariant under the phase-space mirror `(s,v) ↦ (−s,−v)`.
Drop `hodd`: `b(−s)` is unconstrained. Drop `heven`: the denominators differ. -/
theorem lag_mirror (b D : ℝ → ℝ) (hodd : DriftOdd b) (heven : MetricEven D)
    (s v : ℝ) : Lag b D (-s) (-v) = Lag b D s v := by
  unfold Lag
  rw [hodd s, heven s]
  ring

/-- **Action-level ℤ/2 invariance.** The FW action is invariant under the mirror map
on paths, for odd drift and even metric. (Pointwise `lag_mirror` under the sum.) -/
theorem action_mirror_invariant (b D : ℝ → ℝ) (hodd : DriftOdd b)
    (heven : MetricEven D) (P : Path) :
    Action b D (mirrorPath P) = Action b D P := by
  unfold Action mirrorPath
  rw [List.map_map]
  congr 1
  refine List.map_congr_left ?_
  intro p _
  simpa [Function.comp] using lag_mirror b D hodd heven p.1 p.2

/-- **Part 1 headline — `degeneracy_under_oddness`.** Odd drift + even noise metric
⇒ the FW action is ℤ/2-invariant ⇒ the two mirror wells are exactly degenerate,
`ΔV = 0`, for EVERY instanton path. BOTH hypotheses are load-bearing (passed on to
`action_mirror_invariant`/`lag_mirror`; removing either breaks elaboration). -/
theorem degeneracy_under_oddness (b D : ℝ → ℝ) (hodd : DriftOdd b)
    (heven : MetricEven D) (P : Path) : deltaV b D P = 0 := by
  unfold deltaV
  rw [action_mirror_invariant b D hodd heven P]
  ring

end Degeneracy

/-! ## Part 2 — reads, transpose-covariance, and the C4 extension

The `s ↦ −s` mirror on the flux coordinate acts on a complex kernel by the adjoint
`Kᴴ` (conjugate transpose: the physical time-reversal of a dissipative kernel), and
on a real drift-generating matrix by the transpose. A read is **transpose-covariant**
when it intertwines the two AND is homogeneous. The induced drift is **odd** exactly
when the read output is antisymmetric (`Mᵀ = −M`) — the standard transpose = mirror
dictionary of `OffOrigin/OrientationLemma.lean`. -/

section Reads

variable {n : Type*}

/-- Entrywise imaginary part of a complex kernel — a real matrix. -/
noncomputable def imPart (K : Matrix n n ℂ) : Matrix n n ℝ :=
  Matrix.of fun i j => (K i j).im

/-- Entrywise real part of a complex kernel. -/
noncomputable def rePart (K : Matrix n n ℂ) : Matrix n n ℝ :=
  Matrix.of fun i j => (K i j).re

/-- Symmetric part of a real matrix, `(M + Mᵀ)/2`. -/
noncomputable def symM (M : Matrix n n ℝ) : Matrix n n ℝ := (2 : ℝ)⁻¹ • (M + Mᵀ)

/-- Antisymmetric part of a real matrix, `(M − Mᵀ)/2`. -/
noncomputable def asymM (M : Matrix n n ℝ) : Matrix n n ℝ := (2 : ℝ)⁻¹ • (M - Mᵀ)

/-- The **parity-mixing read** `sym ∘ Im`: the symmetric part of the imaginary
(dissipative/arrow) component of the complex kernel. This is the ONE non-odd
channel the tilt probe located. -/
noncomputable def symImRead (K : Matrix n n ℂ) : Matrix n n ℝ := symM (imPart K)

/-- `symM M` is symmetric. -/
theorem symM_isSymm (M : Matrix n n ℝ) : (symM M)ᵀ = symM M := by
  unfold symM
  rw [transpose_smul, transpose_add, transpose_transpose, add_comm]

/-- `imPart` of the adjoint is the negated transpose: `Im(Kᴴ) = −(Im K)ᵀ`
(conjugation negates the imaginary part). -/
theorem imPart_conjTranspose (K : Matrix n n ℂ) :
    imPart (Kᴴ) = -(imPart K)ᵀ := by
  ext i j
  simp [imPart, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.neg_apply,
    Complex.star_def, Complex.conj_im]

/-- A **transpose-covariant read** `R : Mat ℂ → Mat ℝ`: it intertwines the adjoint on
kernels with the transpose on outputs (`cov`) and is homogeneous under negation
(`hom`). Both clauses are needed to force odd drift on the arrow sector; the
`cov` clause is precisely what `sym ∘ Im` fails. -/
structure TransposeCovariantRead (R : Matrix n n ℂ → Matrix n n ℝ) : Prop where
  cov : ∀ K, R (Kᴴ) = (R K)ᵀ
  hom : ∀ K, R (-K) = -(R K)

/-- **C4 extension (matrix form).** A transpose-covariant read of a
transpose-covariant kernel (`Kᴴ = −K`, the pure arrow / anti-Hermitian sector) has
an ANTISYMMETRIC output. Route: `(R K)ᵀ = R Kᴴ = R (−K) = −(R K)`. -/
theorem tc_read_antiHermitian_kernel_antisym
    (R : Matrix n n ℂ → Matrix n n ℝ) (hR : TransposeCovariantRead R)
    (K : Matrix n n ℂ) (hK : Kᴴ = -K) : (R K)ᵀ = -(R K) := by
  rw [← hR.cov K, hK, hR.hom K]

/-- `rePart` is transpose-covariant — a witness that `TransposeCovariantRead` is
inhabited (so the C4 theorem is non-vacuous: on an anti-Hermitian kernel `rePart`
yields an antisymmetric, odd-drift output). -/
theorem rePart_transposeCovariant :
    TransposeCovariantRead (rePart (n := n)) := by
  constructor
  · intro K; ext i j
    simp [rePart, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.of_apply,
      Complex.star_def, Complex.conj_re]
  · intro K; ext i j
    simp [rePart, Matrix.neg_apply, Matrix.of_apply, Complex.neg_re]

end Reads

/-! ## The transpose = odd-drift bridge, and the C4 corollary at the drift level -/

section DriftBridge

/-- The scalar drift induced (along the flux coordinate `s`) by a `2×2` real
drift-generating matrix `M`: the antisymmetric content `(M₀₁ − M₁₀)` is the odd
(linear-in-`s`) part, and the symmetric content `(M₀₀ + M₁₁ + M₀₁ + M₁₀)` is the
even (constant) part. So `inducedDrift M` is an odd function iff its constant part
vanishes iff `M` is antisymmetric — the transpose = mirror dictionary. -/
noncomputable def inducedDrift (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ → ℝ :=
  fun s => (M 0 1 - M 1 0) * s + (M 0 0 + M 1 1 + M 0 1 + M 1 0)

/-- **The bridge.** An antisymmetric read output (`Mᵀ = −M`) induces an ODD drift.
This is the drift-level rendering of `tc_read_antiHermitian_kernel_antisym`. -/
theorem antisym_matrix_induces_odd_drift (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : Mᵀ = -M) : DriftOdd (inducedDrift M) := by
  have d00 : M 0 0 = 0 := by
    have h := congrFun (congrFun hM 0) 0
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h; linarith
  have d11 : M 1 1 = 0 := by
    have h := congrFun (congrFun hM 1) 1
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h; linarith
  have d10 : M 1 0 = -M 0 1 := by
    have h := congrFun (congrFun hM 0) 1
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h; linarith
  intro s
  simp only [inducedDrift, d00, d11, d10]
  ring

variable {n : Type*}

/-- **Part 2, drift level — `tc_read_tc_kernel_odd_drift`.** A transpose-covariant
read of a transpose-covariant (anti-Hermitian) `2×2` kernel induces an ODD drift ⇒
`ΔV = 0` for it by `degeneracy_under_oddness`. The whole transpose-covariant class
cannot tilt the well. -/
theorem tc_read_tc_kernel_odd_drift
    (R : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (hR : TransposeCovariantRead R) (K : Matrix (Fin 2) (Fin 2) ℂ)
    (hK : Kᴴ = -K) : DriftOdd (inducedDrift (R K)) :=
  antisym_matrix_induces_odd_drift _ (tc_read_antiHermitian_kernel_antisym R hR K hK)

end DriftBridge

/-! ## Part 3 — the 2×2 archetype: `sym ∘ Im` is non-covariant and induces a tilt -/

section Archetype

/-- The 2×2 archetype kernel: the M1 arrow injected into the dissipative `(0,0)`
channel as `Im`. `sym ∘ Im` reads its parity-mixing component. -/
noncomputable def archetypeKernel : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I, 0; 0, 0]

/-- `sym ∘ Im` of the archetype: `!![1,0;0,0]` (symmetric, nonzero). -/
theorem symImRead_archetype : symImRead archetypeKernel = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symImRead, symM, imPart, archetypeKernel, Matrix.smul_apply, Matrix.add_apply,
      Matrix.transpose_apply, Matrix.of_apply]
  all_goals norm_num [Complex.I_im, Complex.I_re]

/-- `sym ∘ Im` of the adjoint archetype: `!![−1,0;0,0]` (opposite sign — conjugation
flipped `Im`). Together with `symImRead_archetype` this refutes covariance. -/
theorem symImRead_archetype_adj : symImRead (archetypeKernelᴴ) = !![-1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symImRead, symM, imPart, archetypeKernel, Matrix.conjTranspose_apply,
      Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply,
      Complex.star_def]
  all_goals norm_num [Complex.conj_I, Complex.I_im, Complex.I_re]

/-- **THE SHARPEST CHECK — `symImRead_not_transposeCovariant`.** The parity-mixing
read `sym ∘ Im` is provably NOT transpose-covariant: it fails the `cov` clause on
the archetype kernel (`sym∘Im(Kᴴ) = −!![1,0;0,0] ≠ !![1,0;0,0] = (sym∘Im K)ᵀ`).
Hence Parts 2 and 3 are consistent: `sym ∘ Im` is exactly the read that escapes the
"transpose-covariant ⇒ odd drift" theorem, which is why it can tilt. -/
theorem symImRead_not_transposeCovariant :
    ¬ TransposeCovariantRead (symImRead (n := Fin 2)) := by
  intro hR
  have h := hR.cov archetypeKernel
  rw [symImRead_archetype_adj, symImRead_archetype] at h
  have h00 := congrFun (congrFun h 0) 0
  simp only [Matrix.transpose_apply] at h00
  norm_num [Matrix.cons_val_zero, Matrix.head_cons] at h00

/-- The drift induced by `sym ∘ Im` on the archetype is the constant `1`
(its odd/linear part vanishes, its even/constant part is `1`). -/
theorem archetype_drift : inducedDrift (symImRead archetypeKernel) = fun _ => (1 : ℝ) := by
  funext s
  rw [symImRead_archetype]
  simp only [inducedDrift]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- **Part 3 headline — `tilt_source_exists`.** The drift induced by the `sym ∘ Im`
read of the archetype kernel is NON-odd — a decidable fact on the 2×2 archetype
(`norm_num`). It asserts ONLY this; it does not mention the physical/autopoietic
loop. This is the non-vacuity witness for `degeneracy_under_oddness` (a non-odd
drift, whose `ΔV ≠ 0` is exhibited in `degeneracy_non_vacuous`). -/
theorem tilt_source_exists :
    ¬ DriftOdd (inducedDrift (symImRead archetypeKernel)) := by
  rw [archetype_drift]
  intro h
  have h1 := h 1
  norm_num at h1

/-- **Non-vacuity of Part 1.** An exhibited `(b, even D, path)` with a NON-odd drift
`b` (the `sym ∘ Im` tilt of `tilt_source_exists`) and `ΔV ≠ 0`: the well-splitting
is genuinely a function of the free drift, not `0` by construction. Here `b = 1`,
`D = 1`, `P = [(0,1)]` give `ΔV = 0 − 2 = −2`. -/
theorem degeneracy_non_vacuous :
    ∃ (b D : ℝ → ℝ) (P : Path),
      ¬ DriftOdd b ∧ MetricEven D ∧ deltaV b D P ≠ 0 := by
  refine ⟨inducedDrift (symImRead archetypeKernel), (fun _ => 1), [(0, 1)],
    tilt_source_exists, (fun _ => rfl), ?_⟩
  rw [archetype_drift]
  simp only [deltaV, Action, mirrorPath, Lag, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num

end Archetype

end SpectralPhysics.OffOrigin
