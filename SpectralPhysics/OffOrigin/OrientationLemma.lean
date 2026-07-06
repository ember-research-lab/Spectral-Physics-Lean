/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sign
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

/-!
# The frame-relative orientation invariant σ_P — no-gos + 3×3 orientation lemma

Formalizes the instrument layer of the Krein bridge (companion note:
`spectral_physics/off-origin-directed-side/krein-orientation-note.tex`, spec:
`krein-orientation-lean.tex`). Extends the blindness results of
`OffOrigin/EtaDirIndependence.lean` (C1 `spectral_functional_M2_invariant`,
C2 `triple_invariant_M2_invariant` / `symmetricPart_add_antisymm`) with the first
*positive* result: an explicit transpose-odd functional σ_P that reads the
orientation bit every transpose-invariant functional provably misses.

NOTE: this file deliberately does NOT import `EtaDirIndependence.lean` — that file
carries the OPEN `forward_origin` sorry and is (deliberately) not wired into the
root build; importing it here would pull the sorry into `lake build`. The extension
is mathematical, not module-level.

## Task 1 — No-gos (any dimension)

* `antisymm_charpoly_roots_neg` — core: a complex matrix with `Mᵀ = -M` has
  eigenvalue multiset (charpoly roots) invariant under negation.
* `skew_hermitization_spec_symmetric` — the Hermitianization `i•A` of a real
  antisymmetric `A` has spectrum symmetric under negation (No-go 1: eigenvalue-based
  odd invariants vanish identically).
* `skew_plain_signature_zero` — hence the plain Krein signature (#pos − #neg
  eigenvalues) of `i•A` is identically 0.
* `pfaffian_odd_dim_zero` — `det A = 0` for real antisymmetric `A` in odd dimension.
  Pfaffian corollary (stated here, not formalized — Mathlib has no Pfaffian API, and
  the determinant statement carries the full content in odd dimension): since
  `Pf(A)² = det A`, the Pfaffian branch of the Pfaffian/Krein family is identically
  zero on odd-dimensional carriers; generation space (dim 3) forces the Krein/
  frame-relative branch.

## Task 2 — The 3×3 orientation lemma (generation space, fully concrete)

Sign conventions are LOCKED to the note: `σ_P(H) := sign(Im tr(Pᵀ * H))` for the
Hermitian circulant `H(a,b,c) = a•1 + b•(P+Pᵀ) + (I·c)•(P−Pᵀ)`; with these,
`σ_P(H(a,b,c)) = sign c`.

* `circulant_eigenvalues` — `charpoly H(a,b,c) = ∏ₖ (X − λₖ)`,
  `λₖ = a + 2b·cos(2πk/3) − 2c·sin(2πk/3)`.
* `multiset_blind_to_sign` — the eigenvalue multiset of `H(a,b,c)` equals that of
  `H(a,b,−c)` (the flip *is* the transpose: `H(a,b,c)ᵀ = H(a,b,−c)`).
* `sigma_reads_sign` — `σ_P(H(a,b,c)) = sign c`: reads exactly the bit the
  spectrum cannot.
* `sigma_transpose_odd` — `σ_P(Hᵀ) = −σ_P(H)` for EVERY Hermitian `H` (proved at
  full 3×3 Hermitian generality, not just the circulant family).
* `sigma_symmetric_stable` — σ_P is unchanged by adding any real matrix to `H`
  (proved for ALL real perturbations — symmetry is not even needed, since real
  content cannot enter `Im tr`; the note's circulant-symmetric case is the
  corollary `sigma_circulant_symmetric_stable`).

Numeric anchor for the note's spectrum at `(a,b,c) = (1, 0.35, 0.6)`:
`{1.7, 0.65 − 0.6√3 ≈ −0.389, 0.65 + 0.6√3 ≈ 1.689}` — exact symbolic form proved
(`spectrum_at_note_point`) plus rational brackets (`note_lambda_brackets`).
A literal `#eval` is obstructed by noncomputable ℝ (`Real.sqrt`, `Real.sign`).

Frame-relativity guard: σ_P requires the frame `P` by construction. No frame-free
absolute invariant reading the bit is exhibited anywhere in this file (No-go 1
proves the eigenvalue route cannot supply one) — consistent with C′ externality.
-/

namespace SpectralPhysics.OffOrigin

open Matrix Polynomial

/-! ## Task 1 — No-gos -/

section NoGos

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Hermitianization `i•A` of a real matrix, as a complex matrix. For real
antisymmetric `A` (i.e. `Aᵀ = -A`) this is the Hermitian matrix `iA` of the note. -/
noncomputable def hermitize (A : Matrix n n ℝ) : Matrix n n ℂ :=
  Complex.I • A.map (Complex.ofReal)

omit [Fintype n] [DecidableEq n] in
/-- `i•A` is Hermitian when `A` is real antisymmetric — the object of No-go 1 is
genuinely the Hermitianization. -/
theorem hermitize_isHermitian (A : Matrix n n ℝ) (hA : Aᵀ = -A) :
    (hermitize A).IsHermitian := by
  unfold hermitize
  ext i j
  simp only [conjTranspose_apply, smul_apply, map_apply, smul_eq_mul, star_mul',
    Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  have : Aᵀ i j = -A i j := by rw [hA]; simp
  have hji : A j i = -A i j := by simpa [Matrix.transpose_apply] using this
  rw [hji]
  push_cast
  ring

/-- Sign-collection helper: `(-1)^|s| · ∏_{a∈s} (-x - a) = ∏_{a∈s} (x + a)`. -/
private theorem neg_one_pow_prod_shift (x : ℂ) (s : Multiset ℂ) :
    (-1 : ℂ) ^ Multiset.card s * (s.map fun a => -x - a).prod =
      (s.map fun a => x + a).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    calc (-1 : ℂ) ^ Multiset.card t * -1 * ((-x - a) * (t.map fun b => -x - b).prod)
        = (x + a) * ((-1 : ℂ) ^ Multiset.card t * (t.map fun b => -x - b).prod) := by
          ring
      _ = (x + a) * (t.map fun b => x + b).prod := by rw [ih]

/-- Core of No-go 1, at full generality: a complex matrix with `Mᵀ = -M` has
eigenvalue multiset (= charpoly roots, with multiplicity) invariant under negation.
Route: `charpoly M = charpoly Mᵀ = charpoly (-M)`, and the roots of
`charpoly (-M)` are the negated roots of `charpoly M` (via the monic split
factorization and pointwise evaluation, `Polynomial.funext`). -/
theorem antisymm_charpoly_roots_neg (M : Matrix n n ℂ) (hM : Mᵀ = -M) :
    M.charpoly.roots = M.charpoly.roots.map (fun z => -z) := by
  set p := M.charpoly with hp
  set s := p.roots with hs
  have hmonic : p.Monic := Matrix.charpoly_monic M
  have hsplits : p.Splits := IsAlgClosed.splits p
  -- monic split factorization  p = ∏_{a ∈ roots} (X - C a)
  have hfact : p = (s.map fun a => X - C a).prod :=
    hsplits.eq_prod_roots_of_monic hmonic
  have hcard : Multiset.card s = Fintype.card n := by
    rw [hs, Polynomial.splits_iff_card_roots.mp hsplits, hp,
      Matrix.charpoly_natDegree_eq_dim]
  -- charpoly (-M) is the product over the negated roots (pointwise evaluation)
  have hneg : (-M).charpoly = ((s.map (fun a => -a)).map fun a => X - C a).prod := by
    apply Polynomial.funext
    intro x
    rw [Matrix.eval_charpoly]
    have hmat : Matrix.scalar n x - (-M) = -(Matrix.scalar n (-x) - M) := by
      rw [map_neg]
      abel
    rw [hmat, Matrix.det_neg, ← Matrix.eval_charpoly, ← hp]
    conv_lhs => rw [hfact]
    rw [Polynomial.eval_multiset_prod, Polynomial.eval_multiset_prod,
      Multiset.map_map, Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_neg_eq_add]
    rw [← hcard]
    exact neg_one_pow_prod_shift x s
  have hpeq : p = (-M).charpoly := by
    rw [← hM, hp, Matrix.charpoly_transpose]
  calc p.roots = (-M).charpoly.roots := by rw [hpeq]
    _ = ((s.map (fun a => -a)).map fun a => X - C a).prod.roots := by rw [hneg]
    _ = s.map (fun a => -a) := Polynomial.roots_multiset_prod_X_sub_C _
    _ = p.roots.map (fun z => -z) := by rw [hs]

/-- **No-go 1 (plain Krein signature is dead), spectral form.** For real
antisymmetric `A`, the Hermitianization `i•A` has spectrum (eigenvalue multiset)
symmetric under negation. Hence no eigenvalue-based odd invariant can carry the
orientation bit. -/
theorem skew_hermitization_spec_symmetric (A : Matrix n n ℝ) (hA : Aᵀ = -A) :
    (hermitize A).charpoly.roots = (hermitize A).charpoly.roots.map (fun z => -z) := by
  apply antisymm_charpoly_roots_neg
  unfold hermitize
  rw [transpose_smul, ← Matrix.transpose_map, hA]
  have : ((-A).map (Complex.ofReal) : Matrix n n ℂ) = -(A.map Complex.ofReal) := by
    ext i j; simp
  rw [this, smul_neg]

/-- Signature of an eigenvalue multiset: #(eigenvalues with positive real part)
− #(eigenvalues with negative real part), as an integer. For a Hermitian matrix
(all roots real) this is the usual Krein/inertia signature. -/
noncomputable def rootsSignature (s : Multiset ℂ) : ℤ :=
  ((s.filter (fun z => 0 < z.re)).card : ℤ) - ((s.filter (fun z => z.re < 0)).card : ℤ)

/-- **No-go 1, signature form (`skew_plain_signature_zero`).** The plain signature
of the Hermitianization `i•A` of a real antisymmetric `A` is identically zero:
positive and negative eigenvalues pair off under negation. -/
theorem skew_plain_signature_zero (A : Matrix n n ℝ) (hA : Aᵀ = -A) :
    rootsSignature (hermitize A).charpoly.roots = 0 := by
  classical
  set s := (hermitize A).charpoly.roots with hs
  have hsym : s = s.map (fun z => -z) := skew_hermitization_spec_symmetric A hA
  unfold rootsSignature
  have hpos : s.filter (fun z => 0 < z.re) =
      (s.filter (fun z => z.re < 0)).map (fun z => -z) := by
    conv_lhs => rw [hsym]
    rw [Multiset.filter_map]
    congr 1
    apply Multiset.filter_congr
    intro z _
    constructor
    · intro h; simpa [Complex.neg_re] using h
    · intro h; simpa [Function.comp, Complex.neg_re] using h
  rw [hpos, Multiset.card_map]
  ring

/-- **No-go 2 (Pfaffian is dead on generation space).** `det A = 0` for real
antisymmetric `A` in odd dimension: `det A = det Aᵀ = det (-A) = (-1)ⁿ det A`.
Pfaffian corollary (docstring only — Mathlib has no Pfaffian API, and building one
is out of scope per spec): `Pf(A)² = det A = 0`, so the Pfaffian branch of the
Pfaffian/Krein family vanishes identically on odd-dimensional carriers. Generation
space is 3-dimensional, so on it the orientation invariant *must* be
relative/Krein-class — the frame-relative σ_P below. -/
theorem pfaffian_odd_dim_zero (A : Matrix n n ℝ) (hA : Aᵀ = -A)
    (hodd : Odd (Fintype.card n)) : A.det = 0 := by
  have h1 : A.det = (-A).det := by rw [← hA, Matrix.det_transpose]
  rw [Matrix.det_neg, hodd.neg_one_pow] at h1
  linarith

end NoGos

/-! ## Task 2 — The 3×3 orientation lemma -/

section Orientation3x3

open Complex Real

/-- The generation shift: the 3-cycle permutation matrix `P`, `(P v)_j = v_{j+1}`.
This is the frame supplied by the circulant structure itself. -/
def P3 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 1, 0; 0, 0, 1; 1, 0, 0]

/-- The Hermitian generation-space circulant
`H(a,b,c) = a•1 + b•(P+Pᵀ) + (i·c)•(P−Pᵀ)` (locked sign convention). -/
noncomputable def Hmat (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (a : ℂ) • 1 + (b : ℂ) • (P3 + P3ᵀ) + (Complex.I * c) • (P3 - P3ᵀ)

/-- The frame-relative orientation invariant, Hermitian-circulant form (locked
convention): `σ_P(H) := sign (Im tr (Pᵀ * H))`. Values in `{-1, 0, +1}`; `0` iff
the antisymmetric content vanishes (the bit is *undefined*, not negative, at the
self-adjoint origin). Frame-relativity (the dependence on `P3`) is load-bearing:
it operationalizes the C′ externality result. -/
noncomputable def sigmaP (H : Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  Real.sign ((Matrix.trace (P3ᵀ * H)).im)

/-- Entrywise form of the circulant (all downstream computation routes through
this). -/
theorem Hmat_entries (a b c : ℝ) :
    Hmat a b c =
      !![(a : ℂ), b + Complex.I * c, b - Complex.I * c;
         b - Complex.I * c, a, b + Complex.I * c;
         b + Complex.I * c, b - Complex.I * c, a] := by
  ext i j
  simp only [Hmat, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.transpose_apply, Matrix.one_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [P3] <;> ring

/-- `H(a,b,c)` is Hermitian — the family lives in the self-adjoint layer, where
the C1/C2 blindness theorems apply. -/
theorem Hmat_isHermitian (a b c : ℝ) : (Hmat a b c).IsHermitian := by
  rw [Hmat_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTranspose_apply, Complex.ext_iff]

/-- The `c → -c` flip *is* the transpose: `H(a,b,c)ᵀ = H(a,b,-c)`. This single
identity powers both the multiset blindness (via `charpoly_transpose`) and the
transpose-oddness of σ_P on the family. -/
theorem Hmat_transpose (a b c : ℝ) : (Hmat a b c)ᵀ = Hmat a b (-c) := by
  rw [Hmat_entries, Hmat_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The eigenvalue formula of the note: `λₖ = a + 2b·cos(2πk/3) − 2c·sin(2πk/3)`,
`k ∈ {0,1,2}`. All three are real (as they must be: `H` is Hermitian). -/
noncomputable def eigval (a b c : ℝ) (k : Fin 3) : ℝ :=
  a + 2 * b * Real.cos (2 * Real.pi * k / 3) - 2 * c * Real.sin (2 * Real.pi * k / 3)

theorem eigval_zero (a b c : ℝ) : eigval a b c 0 = a + 2 * b := by
  unfold eigval
  norm_num

theorem eigval_one (a b c : ℝ) : eigval a b c 1 = a - b - Real.sqrt 3 * c := by
  unfold eigval
  have h1 : 2 * Real.pi * ((1 : Fin 3) : ℝ) / 3 = Real.pi - Real.pi / 3 := by
    norm_num; ring
  rw [h1, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  ring

theorem eigval_two (a b c : ℝ) : eigval a b c 2 = a - b + Real.sqrt 3 * c := by
  unfold eigval
  have h2 : 2 * Real.pi * ((2 : Fin 3) : ℝ) / 3 = Real.pi + Real.pi / 3 := by
    norm_num; ring
  rw [h2, Real.cos_add, Real.sin_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  ring

/-- **Orientation lemma (i) — `circulant_eigenvalues`.** The characteristic
polynomial of `H(a,b,c)` factors as `∏ₖ (X − λₖ)` with
`λₖ = a + 2b·cos(2πk/3) − 2c·sin(2πk/3)` — the Fourier diagonalization of the
3×3 circulant, fully concrete. -/
theorem circulant_eigenvalues (a b c : ℝ) :
    (Hmat a b c).charpoly =
      (X - C (eigval a b c 0 : ℂ)) * (X - C (eigval a b c 1 : ℂ)) *
        (X - C (eigval a b c 2 : ℂ)) := by
  rw [eigval_zero, eigval_one, eigval_two]
  apply Polynomial.funext
  intro x
  rw [Matrix.eval_charpoly]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hs : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  rw [Hmat_entries]
  simp only [Matrix.det_fin_three, Matrix.sub_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  norm_num
  push_cast
  linear_combination (3 * (c : ℂ) ^ 2 * (x - a - 2 * b)) * hI +
    ((c : ℂ) ^ 2 * (x - a - 2 * b)) * hs

/-- Roots-multiset form: `spec H(a,b,c) = {λ₀, λ₁, λ₂}` with multiplicity. -/
theorem circulant_roots (a b c : ℝ) :
    (Hmat a b c).charpoly.roots =
      {(eigval a b c 0 : ℂ), (eigval a b c 1 : ℂ), (eigval a b c 2 : ℂ)} := by
  rw [circulant_eigenvalues]
  have h0 : (X - C (eigval a b c 0 : ℂ)) ≠ 0 := Polynomial.X_sub_C_ne_zero _
  have h1 : (X - C (eigval a b c 1 : ℂ)) ≠ 0 := Polynomial.X_sub_C_ne_zero _
  have h2 : (X - C (eigval a b c 2 : ℂ)) ≠ 0 := Polynomial.X_sub_C_ne_zero _
  rw [Polynomial.roots_mul (mul_ne_zero (mul_ne_zero h0 h1) h2),
    Polynomial.roots_mul (mul_ne_zero h0 h1),
    Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
  rfl

/-- **Orientation lemma (ii) — `multiset_blind_to_sign`.** The eigenvalue multiset
of `H(a,b,c)` equals that of `H(a,b,−c)`: the spectrum — hence every spectral
functional and the mass multiset itself — is blind to `sign c`. Proved at
polynomial level (charpolys are *equal*), via the identity `H(a,b,−c) = H(a,b,c)ᵀ`:
the chamber flip is literally the transpose, which extends C1/C2 to the
generation-space chamber structure. (The Fourier relabeling `k ↔ 3−k` witness is
visible in `circulant_roots`: `λₖ(−c) = λ₍₃₋ₖ₎(c)`.) -/
theorem multiset_blind_to_sign (a b c : ℝ) :
    (Hmat a b (-c)).charpoly.roots = (Hmat a b c).charpoly.roots := by
  rw [← Hmat_transpose, Matrix.charpoly_transpose]

/-- Trace pairing computation: `tr(Pᵀ · H(a,b,c)) = 3b + 3ic`, so
`Im tr(Pᵀ H) = 3c`. -/
theorem trace_pairing (a b c : ℝ) :
    (Matrix.trace (P3ᵀ * Hmat a b c)).im = 3 * c := by
  rw [Hmat_entries]
  simp [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, P3,
    Complex.add_im, Complex.mul_im]
  ring

/-- `sign(3c) = sign(c)` helper. -/
private theorem sign_three_mul (c : ℝ) : Real.sign (3 * c) = Real.sign c := by
  rcases lt_trichotomy c 0 with h | h | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (by linarith)]
  · rw [h]; norm_num
  · rw [Real.sign_of_pos h, Real.sign_of_pos (by linarith)]

/-- **Orientation lemma (iii) — `sigma_reads_sign`.** `σ_P(H(a,b,c)) = sign c`:
the frame-relative invariant reads exactly the bit the spectrum cannot
(cf. `multiset_blind_to_sign`). -/
theorem sigma_reads_sign (a b c : ℝ) : sigmaP (Hmat a b c) = Real.sign c := by
  unfold sigmaP
  rw [trace_pairing, sign_three_mul]

/-- **Orientation lemma (iv) — `sigma_transpose_odd`.** `σ_P(Hᵀ) = −σ_P(H)` for
*every* Hermitian 3×3 `H` (full Hermitian generality, not just the circulant
family): σ_P is orientation-sensitive precisely where every C1/C2-covered
functional is even. It evades the blindness theorems legitimately — it is a
functional of the antisymmetric content and the frame, not of the spectrum. -/
theorem sigma_transpose_odd (H : Matrix (Fin 3) (Fin 3) ℂ) (hH : H.IsHermitian) :
    sigmaP Hᵀ = -sigmaP H := by
  have h01 : star (H 0 1) = H 1 0 := hH.apply 1 0
  have h12 : star (H 1 2) = H 2 1 := hH.apply 2 1
  have h20 : star (H 2 0) = H 0 2 := hH.apply 0 2
  have key : (Matrix.trace (P3ᵀ * Hᵀ)).im = -(Matrix.trace (P3ᵀ * H)).im := by
    simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.transpose_apply, P3, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
    rw [← h01, ← h12, ← h20]
    simp [Complex.add_im]
    ring
  unfold sigmaP
  rw [key, Real.sign_neg]

/-- Transpose-oddness on the circulant family, as a corollary (with
`sign(−c) = −sign c` made explicit). -/
theorem sigma_transpose_odd_circulant (a b c : ℝ) :
    sigmaP (Hmat a b c)ᵀ = -sigmaP (Hmat a b c) :=
  sigma_transpose_odd (Hmat a b c) (Hmat_isHermitian a b c)

/-- **Orientation lemma (v) — `sigma_symmetric_stable`.** σ_P is unchanged by
adding *any* real matrix to the generator — real content cannot enter
`Im tr(Pᵀ ·)`. This is strictly more general than the note's "real symmetric
perturbation" (symmetry is not needed): σ_P is a pure-M2 readout relative to the
frame. -/
theorem sigma_symmetric_stable (H : Matrix (Fin 3) (Fin 3) ℂ)
    (S : Matrix (Fin 3) (Fin 3) ℝ) :
    sigmaP (H + S.map (Complex.ofReal)) = sigmaP H := by
  have hS : (Matrix.trace (P3ᵀ * S.map (Complex.ofReal))).im = 0 := by
    simp [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, P3,
      Complex.add_im]
  unfold sigmaP
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_im, hS, add_zero]

/-- The load-bearing minimum of the note: stability under circulant-symmetric
perturbations `S = a'•1 + b'•(P+Pᵀ)` (i.e. `Hmat a' b' 0`), phrased inside the
family: `σ_P(H(a,b,c) + H(a',b',0)) = σ_P(H(a,b,c)) = sign c`. -/
theorem sigma_circulant_symmetric_stable (a b c a' b' : ℝ) :
    sigmaP (Hmat a b c + Hmat a' b' 0) = sigmaP (Hmat a b c) := by
  have hsum : Hmat a b c + Hmat a' b' 0 = Hmat (a + a') (b + b') c := by
    rw [Hmat_entries, Hmat_entries, Hmat_entries]
    ext i j
    simp only [Matrix.add_apply]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  rw [hsum, sigma_reads_sign, sigma_reads_sign]

/-! ### Numeric anchor (the note's spectrum at `(a,b,c) = (1, 0.35, 0.6)`)

`#eval`/`decide` is obstructed by noncomputable ℝ (`Real.sqrt`, `Real.sin`,
`Real.sign` carry no executable code), so the check is done as proved exact
symbolic values plus rational brackets reproducing the note's
`{−0.389…, 1.689…, 1.7}`. -/

/-- Exact spectrum at the note's point: `{1.7, 0.65 − √3·0.6, 0.65 + √3·0.6}`. -/
theorem spectrum_at_note_point :
    (Hmat 1 0.35 0.6).charpoly.roots =
      {((1.7 : ℝ) : ℂ), ((0.65 - Real.sqrt 3 * 0.6 : ℝ) : ℂ),
        ((0.65 + Real.sqrt 3 * 0.6 : ℝ) : ℂ)} := by
  rw [circulant_roots, eigval_zero, eigval_one, eigval_two]
  norm_num

/-- Rational brackets: `−0.39 < 0.65 − √3·0.6 < −0.38` and
`1.68 < 0.65 + √3·0.6 < 1.69`, matching the note's `−0.389…` and `1.689…`
(via `1.7320 < √3 < 1.7321`). -/
theorem note_lambda_brackets :
    (-0.39 < 0.65 - Real.sqrt 3 * 0.6 ∧ 0.65 - Real.sqrt 3 * 0.6 < -0.38) ∧
      (1.68 < 0.65 + Real.sqrt 3 * 0.6 ∧ 0.65 + Real.sqrt 3 * 0.6 < 1.69) := by
  have hlow : (1.7320 : ℝ) < Real.sqrt 3 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hhigh : Real.sqrt 3 < 1.7321 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

end Orientation3x3

/-! ### Axiom audit (compile-time)

Every closed lemma above must trace to at most the three standard Mathlib
axioms (`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no new
axioms. Recorded in `OffOrigin/STATUS.md`. -/
#print axioms antisymm_charpoly_roots_neg
#print axioms skew_hermitization_spec_symmetric
#print axioms skew_plain_signature_zero
#print axioms pfaffian_odd_dim_zero
#print axioms hermitize_isHermitian
#print axioms circulant_eigenvalues
#print axioms circulant_roots
#print axioms multiset_blind_to_sign
#print axioms sigma_reads_sign
#print axioms sigma_transpose_odd
#print axioms sigma_transpose_odd_circulant
#print axioms sigma_symmetric_stable
#print axioms sigma_circulant_symmetric_stable
#print axioms spectrum_at_note_point
#print axioms note_lambda_brackets

end SpectralPhysics.OffOrigin
