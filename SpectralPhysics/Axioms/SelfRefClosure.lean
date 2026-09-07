/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Axioms.Laplacian
import SpectralPhysics.Axioms.RelativeSpectrum
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.Interval.Finset.Fin

/-
  Axioms/SelfRefClosure.lean — Abstract Axiom 3 (Self-Referential Closure)

  The most abstract formulation of Axiom 3, independent of any specific
  application. The core principle:

    "If a structure is type-compatible with the algebra,
     it is detectable by the functional. Nothing compatible can hide."

  This file provides:
  1. The abstract algebraic framework (StarAlgebraWithState)
  2. The three conditions of Axiom 3 as independent typeclasses
  3. Algebraic closure (meta-observation terminates)
  4. The completeness theorem: closure + faithfulness => no ghosts
  5. Stability above the complexity threshold I*
  6. Instance: Spectral physics (trace on observation algebra)
  7. Abstract interface for external instances (Hodge, etc.)
  8. **Axiom 3 in the manuscript's 2026-09-06 form (Spectral Faithfulness):**
     the TWO-PIECE self-model map
       M : (A, H, L) ↦ (ζ_L, Spec_N(A))
     and the faithfulness predicate "M admits a reconstruction operator R
     with R ∘ M = id" (`SelfModelMap.SpectrallyFaithful`). Finite
     dimensions: ζ_L = the eigenvalue list (`zetaPiece`), Spec_N(A) = the
     gauge class of the eigenbasis-to-A-basis unitary
     (`Axioms/RelativeSpectrum.lean`). The reconstruction is a theorem
     (`reconstruct_selfModel`, T1: the matrix spectral theorem).

  STATUS OF SECTIONS 1–7 (2026-09-06): these encode the EARLIER, trace-state
  statement of Axiom 3 (three conditions on the trace as a state on A_obs)
  and the ONE-PIECE first component only: `SpectralData n` is the sorted
  eigenvalue list = ζ_L in finite dimensions, and `SpectralDetermination`
  says that the trace functional determines that list. The manuscript
  (`ax:self-ref`, `def:self-model-map-axioms-stub`) now states the axiom
  on the pair (ζ_L, Spec_N(A)); Section 8 is the authoritative encoding.
  Sections 1–7 are kept because downstream modules import them; they are
  not deleted or re-derived here.

  Dependencies: Axioms/RelationalStructure, Axioms/Laplacian,
                Axioms/RelativeSpectrum

  References:
    Manuscript v0.8, lines 285-304 (Axiom 3)
    Manuscript v0.8, lines 5485-5491 (Algebraic closure definition)
    Manuscript main c558e6e (2026-09-06): §"Axiom 3: Spectral Faithfulness",
      Definition def:self-model-map-axioms-stub, Axiom ax:self-ref
    Connes, "A unitary invariant in Riemannian geometry", arXiv:0810.2091, Def 2.5
-/

-- ============================================================================
-- SECTION 0: THE ABSTRACT PRINCIPLE
-- ============================================================================

/-
  The abstract content of Axiom 3, stripped of all physics:

  Given:
    - An algebra A (with involution *)
    - A positive linear functional w : A -> R

  Faithfulness: w(a* a) > 0 for every nonzero a
  Completeness: the algebra contains everything type-compatible
  Detection: faithfulness + completeness => nothing type-compatible
             is a ghost (present but invisible)
-/

/-- A *-algebra over R with a positive linear functional (state). -/
class StarAlgebraWithState (A : Type*) extends Mul A, Add A, Star A, Zero A where
  /-- The state functional w : A -> R -/
  state : A → ℝ
  /-- w is positive: w(a* a) >= 0 -/
  state_nonneg : ∀ a : A, state (star a * a) ≥ 0
  /-- w is nondegenerate -/
  state_nonzero : ∃ a : A, state (star a * a) > 0

-- ============================================================================
-- SECTION 1: THE THREE CONDITIONS (INDEPENDENT TYPECLASSES)
-- ============================================================================

/-
  Axiom 3 decomposes into three logically independent conditions.
  Different downstream theorems use different conditions:

  - Division algebra forcing: AlgebraicallyClosed
  - Gap inheritance (alpha_s, Lambda_cosmo): SectorFaithful
  - Spectral convergence non-collapse: TraceFaithful
  - Spectrum recovery: SpectralDetermination
-/

/-- The spectral data of a self-adjoint operator.

2026-09-06: this is the FIRST PIECE ONLY of the self-model map (ζ_L as a sorted
eigenvalue list). The two-piece map lives in Section 8 (`SelfModelMap.selfModel`). -/
structure SpectralData (n : ℕ) where
  /-- Eigenvalues, indexed -/
  eigenvalues : Fin n → ℝ
  /-- Eigenvalues are non-negative (from Axiom 2: L >= 0) -/
  eigenvalues_nonneg : ∀ i, eigenvalues i ≥ 0
  /-- Eigenvalues are sorted -/
  eigenvalues_sorted : ∀ i j, i ≤ j → eigenvalues i ≤ eigenvalues j

variable {n : ℕ}

/-- The trace functional: Tr(g(L)) = sum g(lambda_k). -/
def spectralTrace (S : SpectralData n) (g : ℝ → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun i => g (S.eigenvalues i))

/--
  Condition (i): DETERMINATION

  The map g |-> Tr(g(L)) determines the spectrum {lambda_k}.

  Finite dim: theorem (Newton's identities).
  Infinite dim: genuine constraint (forces compact resolvent).

  2026-09-06: this is a ONE-PIECE statement (trace data ⇒ eigenvalue list). It
  says nothing about the relative spectrum; in particular it does NOT assert
  that the eigenvalue list determines the structure — that assertion is
  false (cospectral pairs; see `Examples/SelfModelVacuity.lean`,
  `not_zetaFaithful_pair`). The faithfulness of Axiom 3 is
  `SelfModelMap.SpectrallyFaithful` (Section 8).
-/
class SpectralDetermination (S : SpectralData n) : Prop where
  determines : ∀ S' : SpectralData n,
    (∀ g : ℝ → ℝ, spectralTrace S g = spectralTrace S' g) →
    S.eigenvalues = S'.eigenvalues

/--
  Condition (ii): POSITIVITY / FAITHFULNESS

  The trace defines a faithful state on the observation algebra.
  For every nonzero a in A_obs, w(a*a) > 0.

  GNS language: w is faithful, pi_w is injective.
-/
class TraceFaithful (A : Type*) [StarAlgebraWithState A] : Prop where
  pos : ∀ a : A, a ≠ 0 → StarAlgebraWithState.state (star a * a) > 0

/--
  Condition (iii): SECTOR FAITHFULNESS

  For A = A_1 tensor A_2 tensor ... tensor A_k, partial traces are faithful
  on each individual factor.

  Strictly stronger than (ii). No sector hides behind others.
-/
class SectorFaithful
    (A₁ A₂ A₃ : Type*)
    [StarAlgebraWithState A₁] [StarAlgebraWithState A₂] [StarAlgebraWithState A₃]
    : Prop where
  factor1_faithful : TraceFaithful A₁
  factor2_faithful : TraceFaithful A₂
  factor3_faithful : TraceFaithful A₃

-- ============================================================================
-- SECTION 2: ALGEBRAIC CLOSURE
-- ============================================================================

/-
  The algebraic closure condition (Ch 22, line 5485):
  Meta-observation generates no new structure.

  Independent of conditions (i)-(iii). Constrains the algebra A
  itself, not the pair (A, w).
-/

/-- An algebra supports meta-observation. -/
class MetaObservable (A : Type*) where
  /-- The meta-observation extension -/
  metaExtend : Type*
  /-- A embeds into its extension -/
  embed : A → metaExtend

/-- Algebraic closure: meta-observation terminates. -/
class AlgebraicallyClosed (A : Type*) [MetaObservable A] : Prop where
  closed : Nonempty (MetaObservable.metaExtend (A := A) ≃ A)

-- ============================================================================
-- SECTION 3: THE COMPLETENESS PRINCIPLE
-- ============================================================================

/--
  Algebraic closure + faithfulness => no ghosts.

  Trivial given the premises. The content is in establishing
  the premises for specific instances.
-/
theorem completeness_no_ghosts
    (A : Type*) [StarAlgebraWithState A] [MetaObservable A]
    [AlgebraicallyClosed A] [hf : TraceFaithful A] :
    ∀ a : A, a ≠ 0 → StarAlgebraWithState.state (star a * a) > 0 :=
  fun a ha => hf.pos a ha

-- ============================================================================
-- SECTION 4: STABILITY ABOVE THE COMPLEXITY THRESHOLD
-- ============================================================================

/-
  Phase transition:
  - Below I*: faithfulness fragile
  - At transition: unstable
  - Above I*: stable, self-correcting (spectral gap -> exponential recovery)
-/

/-- Integration capacity: spectral complexity measure. -/
noncomputable def integrationCapacity (S : SpectralData n) : ℝ :=
  spectralTrace S (fun x => if x > 0 then 1 / x else 0)

/-- The complexity threshold I*. -/
class ComplexityThreshold (n : ℕ) where
  iStar : ℝ
  iStar_pos : iStar > 0

/-- Above I*, faithfulness is stable under perturbation.
    Requires n >= 2 so that the first nonzero eigenvalue exists. -/
class StableFaithfulness (S : SpectralData n) (A : Type*)
    [StarAlgebraWithState A] [ComplexityThreshold n] (hn : n ≥ 2) : Prop where
  above_threshold : integrationCapacity S > ComplexityThreshold.iStar (n := n)
  faithful : TraceFaithful A
  spectral_gap_pos : S.eigenvalues ⟨1, by omega⟩ > 0

-- ============================================================================
-- SECTION 5: THE FULL AXIOM
-- ============================================================================

/-- Self-Referential Closure (Axiom 3): conjunction of all conditions.
    Import individual conditions when possible. -/
class SelfRefClosure
    (S : SpectralData n)
    (A : Type*)
    [StarAlgebraWithState A] [MetaObservable A] : Prop where
  determination : SpectralDetermination S
  faithfulness : TraceFaithful A
  sectorFaithful : ∃ (A₁ A₂ A₃ : Type*)
    (_ : StarAlgebraWithState A₁)
    (_ : StarAlgebraWithState A₂)
    (_ : StarAlgebraWithState A₃),
    SectorFaithful A₁ A₂ A₃
  closure : AlgebraicallyClosed A

-- ============================================================================
-- SECTION 6: SPECTRAL PHYSICS INSTANCE
-- ============================================================================

/-- **Sorted sequences with equal counting functions are equal.**
For f, g : Fin n → ℝ both sorted (monotone), if for all a ∈ ℝ
the number of indices k with f(k) ≤ a equals the number with g(k) ≤ a,
then f = g pointwise.

Proof: by contradiction. If f(i) ≠ g(i) at some i, WLOG f(i) < g(i).
Take a = f(i). Then #{k : f(k) ≤ a} ≥ i+1 (sorted: k ≤ i ⟹ f(k) ≤ f(i) = a).
But #{k : g(k) ≤ a} ≤ i (sorted: k ≥ i ⟹ g(k) ≥ g(i) > a). Contradiction. -/
private theorem sorted_eq_of_count_eq
    (f g : Fin n → ℝ)
    (hf : ∀ i j : Fin n, i ≤ j → f i ≤ f j)
    (hg : ∀ i j : Fin n, i ≤ j → g i ≤ g j)
    (h_count : ∀ a : ℝ,
      Finset.card (Finset.univ.filter (fun k : Fin n => f k ≤ a)) =
      Finset.card (Finset.univ.filter (fun k : Fin n => g k ≤ a))) :
    f = g := by
  ext i
  by_contra h_ne
  rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
  · -- f(i) < g(i): take a = f(i)
    have h := h_count (f i)
    -- Lower bound on #{k : f(k) ≤ f(i)}: contains all k ≤ i (sorted)
    have h_sub : Finset.Iic i ⊆
        Finset.univ.filter (fun k : Fin n => f k ≤ f i) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hf k i (Finset.mem_Iic.mp hk)
    -- Upper bound on #{k : g(k) ≤ f(i)}: excludes all k ≥ i (sorted + g(i) > f(i))
    have h_sub' : Finset.univ.filter (fun k : Fin n => g k ≤ f i) ⊆
        Finset.Iio i := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simp only [Finset.mem_Iio]
      by_contra h_ge
      push_neg at h_ge
      exact not_le.mpr h_lt (le_trans (hg i k h_ge) hk)
    have h1 := Finset.card_le_card h_sub
    have h2 := Finset.card_le_card h_sub'
    simp only [Fin.card_Iic, Fin.card_Iio] at h1 h2
    omega
  · -- g(i) < f(i): symmetric
    have h := h_count (g i)
    have h_sub : Finset.Iic i ⊆
        Finset.univ.filter (fun k : Fin n => g k ≤ g i) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hg k i (Finset.mem_Iic.mp hk)
    have h_sub' : Finset.univ.filter (fun k : Fin n => f k ≤ g i) ⊆
        Finset.Iio i := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simp only [Finset.mem_Iio]
      by_contra h_ge
      push_neg at h_ge
      exact not_le.mpr h_gt (le_trans (hf i k h_ge) hk)
    have h1 := Finset.card_le_card h_sub
    have h2 := Finset.card_le_card h_sub'
    simp only [Fin.card_Iic, Fin.card_Iio] at h1 h2
    omega

/-- In finite dimensions, determination is a theorem.

The hypothesis `∀ g, Σ g(λ_k) = Σ g(λ'_k)` for ALL g : ℝ → ℝ is very strong.
Specializing to `g(x) = (x - c)^2` and setting `c = S.eigenvalues i` gives
`Σ_k (S.eigenvalues k - S.eigenvalues i)^2 = Σ_k (S'.eigenvalues k - S.eigenvalues i)^2`.
The k = i term on the LHS is 0. Combined with non-negativity and sorting,
this forces `S'.eigenvalues i = S.eigenvalues i`. -/
theorem spectral_determination_finite (S : SpectralData n) :
    SpectralDetermination S := by
  constructor
  intro S' hg
  -- Use sorted_eq_of_count_eq: sorted sequences with equal counting functions are equal.
  -- Get counting function equality from hg with indicator functions.
  apply sorted_eq_of_count_eq S.eigenvalues S'.eigenvalues
    S.eigenvalues_sorted S'.eigenvalues_sorted
  intro a
  -- Specialize hg to g(x) = if x ≤ a then 1 else 0
  have h := hg (fun x => if x ≤ a then 1 else 0)
  simp only [spectralTrace, Finset.sum_boole] at h
  exact_mod_cast h

/-- Gap inheritance: sector faithfulness propagates individual sector gaps. -/
theorem gap_inheritance
    {A₁ A₂ A₃ : Type*}
    [StarAlgebraWithState A₁] [StarAlgebraWithState A₂] [StarAlgebraWithState A₃]
    [sf : SectorFaithful A₁ A₂ A₃]
    (a : A₁) (ha : a ≠ 0) :
    StarAlgebraWithState.state (star a * a) > 0 :=
  sf.factor1_faithful.pos a ha

-- ============================================================================
-- SECTION 7: ABSTRACT INTERFACE FOR EXTERNAL INSTANCES
-- ============================================================================

/-
  Any instance of the completeness principle must provide:
  1. An algebra A (the "algebraic side")
  2. A functional w on A (the "detection mechanism")
  3. A proof of algebraic closure (the algebra is complete)
  4. A proof (or conjecture) of faithfulness (the functional detects all)

  Instances: Hodge.lean, and potentially Langlands.lean,
  RiemannHypothesis.lean, PvsNP.lean.
-/

/-- A Completeness Instance packages all data for the principle. -/
structure CompletenessInstance where
  Algebra : Type*
  algState : StarAlgebraWithState Algebra
  metaObs : MetaObservable Algebra
  isClosed : @AlgebraicallyClosed Algebra metaObs
  isFaithful : @TraceFaithful Algebra algState

-- ============================================================================
-- SECTION 8: AXIOM 3 (2026-09-06 FORM) — THE TWO-PIECE SELF-MODEL MAP
-- ============================================================================

/-
  Manuscript (main c558e6e, `def:self-model-map-axioms-stub`, `ax:self-ref`):

    M : (A, H, L) ↦ (ζ_L, Spec_N(A))

  A physical relational structure is one whose self-model map admits a
  reconstruction operator R with R ∘ M = id.

  Finite-dimensional encoding (matches `RelationalStructure`: X finite):
    * A finite spectral triple is a Hermitian matrix L in the labelled
      A-basis δ̂_x (`FiniteTriple X`); a relational structure gives one via
      `RelationalStructure.laplacianMatrix` (Axioms/RelativeSpectrum.lean).
    * Piece 1, `zetaPiece T = T.2.eigenvalues : X → ℝ` — mathlib's eigenvalue
      list of the Hermitian matrix (sorted decreasingly and transported along a
      fixed enumeration of X, so equal lists ⇔ equal charpoly ⇔ equal spectrum
      with multiplicity: `Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff`).
      In finite dimensions this IS ζ_L: ζ_L(s) = Σ λ_k^{-s} is determined by
      and determines the list.
    * Piece 2, `⟦eigenChart T⟧ : RelativeSpectrum X` — the gauge class of
      mathlib's eigenvector unitary, labelled by the eigenvalues.
    * `reconstruct` : (ζ, Spec_N) ↦ Σ_t t · f_t = L. `reconstruct_selfModel`
      (T1) is the matrix spectral theorem; hence `SpectrallyFaithful` holds
      for every class of finite triples, while the one-piece predicate
      `ZetaFaithful` fails on any cospectral pair (`not_zetaFaithful_of_cospectral`).

  Not formalised here: infinite dimensions, meromorphic ζ, Connes'
  reconstruction theorem on manifolds, and clause (ii) (naturality) of
  `ax:self-ref`.
-/

open Matrix

noncomputable section

namespace SelfModelMap

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The two-piece self-model `(ζ_L, Spec_N(A))` of a finite spectral triple. -/
@[ext]
structure SelfModel (X : Type*) [Fintype X] [DecidableEq X] where
  /-- Piece 1: the eigenvalue list (finite ζ_L). -/
  zeta : X → ℝ
  /-- Piece 2: the relative spectrum (gauge class of the eigenbasis chart). -/
  relSpec : RelativeSpectrum X

/-- A finite spectral triple `(A, H, L)` with `A = C(X)` diagonal in the labelled
basis of `H = ℂ^X`: the data is the Hermitian matrix `L`. -/
abbrev FiniteTriple (X : Type*) [Fintype X] [DecidableEq X] := {L : Matrix X X ℂ // L.IsHermitian}

instance : Inhabited (FiniteTriple X) := ⟨⟨0, Matrix.isHermitian_zero⟩⟩

/-- The eigen-chart of a finite triple: mathlib's eigenvalue labelling and
eigenvector unitary (a choice; its gauge class is canonical). -/
def eigenChart (T : FiniteTriple X) : EigenChart X :=
  ⟨T.2.eigenvalues, (T.2.eigenvectorUnitary : Matrix X X ℂ), T.2.eigenvectorUnitary.2⟩

/-- **The self-model map** `M : (A, H, L) ↦ (ζ_L, Spec_N(A))`. -/
def selfModel (T : FiniteTriple X) : SelfModel X :=
  ⟨T.2.eigenvalues, ⟦eigenChart T⟧⟩

/-- The ONE-PIECE map `L ↦ ζ_L` (eigenvalue list only) — the form superseded on
2026-09-06; kept as the object the vacuity tests refute. -/
def zetaPiece (T : FiniteTriple X) : X → ℝ := T.2.eigenvalues

/-- Reconstruction from the two pieces: `L = Σ_{t ∈ spectrum} t · f_t`, with `f_t`
the eigenprojections carried by the relative spectrum. -/
def reconstruct (m : SelfModel X) : Matrix X X ℂ :=
  ∑ t ∈ Finset.univ.image m.zeta, (t : ℂ) • m.relSpec.proj t

/-- [T1] `R ∘ M = id` on finite triples (matrix spectral theorem). -/
theorem reconstruct_selfModel (T : FiniteTriple X) : reconstruct (selfModel T) = T.1 := by
  set U : Matrix X X ℂ := (T.2.eigenvectorUnitary : Matrix X X ℂ) with hU
  have key : ∑ t ∈ Finset.univ.image T.2.eigenvalues, (t : ℂ) • indicator T.2.eigenvalues t
      = diagonal (RCLike.ofReal ∘ T.2.eigenvalues) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, indicator, diagonal_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp only [if_true, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      simp
    · simp [hij]
  calc reconstruct (selfModel T)
      = ∑ t ∈ Finset.univ.image T.2.eigenvalues,
          (t : ℂ) • (U * indicator T.2.eigenvalues t * star U) := rfl
    _ = U * (∑ t ∈ Finset.univ.image T.2.eigenvalues, (t : ℂ) • indicator T.2.eigenvalues t)
          * star U := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = U * diagonal (RCLike.ofReal ∘ T.2.eigenvalues) * star U := by rw [key]
    _ = T.1 := by
        conv_rhs => rw [T.2.spectral_theorem]
        rfl

/-- "The map `M` admits a reconstruction operator on the class `𝒞`":
`∃ R, ∀ T ∈ 𝒞, R (M T) = T` — clause (i) of `ax:self-ref`. -/
def AdmitsReconstruction {β : Type*} (M : FiniteTriple X → β) (𝒞 : Set (FiniteTriple X)) : Prop :=
  ∃ R : β → FiniteTriple X, ∀ T ∈ 𝒞, R (M T) = T

/-- [T1] Admitting a reconstruction operator on `𝒞` is exactly injectivity on `𝒞`. -/
theorem admitsReconstruction_iff_injOn {β : Type*} (M : FiniteTriple X → β)
    (𝒞 : Set (FiniteTriple X)) : AdmitsReconstruction M 𝒞 ↔ Set.InjOn M 𝒞 := by
  constructor
  · rintro ⟨R, hR⟩ a ha b hb hab
    rw [← hR a ha, ← hR b hb, hab]
  · intro hinj
    exact ⟨Function.invFunOn M 𝒞, fun T hT => hinj.leftInvOn_invFunOn hT⟩

/-- **Axiom 3, Spectral Faithfulness (clause (i))**, finite form: the two-piece
self-model map admits a reconstruction operator on the class `𝒞`. -/
def SpectrallyFaithful (𝒞 : Set (FiniteTriple X)) : Prop := AdmitsReconstruction selfModel 𝒞

/-- The one-piece (ζ-only) faithfulness predicate — the superseded form. -/
def ZetaFaithful (𝒞 : Set (FiniteTriple X)) : Prop := AdmitsReconstruction zetaPiece 𝒞

/-- The reconstruction operator `R`, as a map into finite triples. -/
def reconstructionOperator (m : SelfModel X) : FiniteTriple X :=
  if h : (reconstruct m).IsHermitian then ⟨reconstruct m, h⟩ else default

theorem reconstructionOperator_selfModel (T : FiniteTriple X) :
    reconstructionOperator (selfModel T) = T := by
  have h : (reconstruct (selfModel T)).IsHermitian := by rw [reconstruct_selfModel]; exact T.2
  unfold reconstructionOperator
  rw [dif_pos h]
  exact Subtype.ext (reconstruct_selfModel T)

/-- [T1] Every class of finite triples is spectrally faithful for the two-piece map:
in finite dimensions Axiom 3 (i) is a theorem, not a constraint. -/
theorem spectrallyFaithful (𝒞 : Set (FiniteTriple X)) : SpectrallyFaithful 𝒞 :=
  ⟨reconstructionOperator, fun T _ => reconstructionOperator_selfModel T⟩

/-- [T1] The two-piece self-model map is injective. -/
theorem selfModel_injective : Function.Injective (selfModel (X := X)) := fun a b h => by
  have := congrArg reconstructionOperator h
  rwa [reconstructionOperator_selfModel, reconstructionOperator_selfModel] at this

/-- [T1] The one-piece map is NOT faithful on any cospectral pair of distinct triples. -/
theorem not_zetaFaithful_of_cospectral {T T' : FiniteTriple X} (hne : T ≠ T')
    (hz : zetaPiece T = zetaPiece T') : ¬ ZetaFaithful {T, T'} := by
  rintro ⟨R, hR⟩
  apply hne
  rw [← hR T (by simp), ← hR T' (by simp), hz]

/-- [T1] On a cospectral pair of distinct triples the SECOND piece is what separates. -/
theorem relSpec_ne_of_cospectral {T T' : FiniteTriple X} (hne : T ≠ T')
    (hz : zetaPiece T = zetaPiece T') : (selfModel T).relSpec ≠ (selfModel T').relSpec := by
  intro h
  exact hne (selfModel_injective (SelfModel.ext hz h))

end SelfModelMap

namespace RelationalStructure

/-- The finite spectral triple `(C(X), L²(X, μ), 𝓛)` of a relational structure,
in the orthonormal basis `δ̂_x`. -/
def toFiniteTriple (S : RelationalStructure) : SelfModelMap.FiniteTriple S.X :=
  ⟨S.laplacianMatrix, S.laplacianMatrix_isHermitian⟩

/-- The self-model `M(X, μ, k) = (ζ_𝓛, Spec_N(C(X)))` of a relational structure. -/
def selfModel (S : RelationalStructure) : SelfModelMap.SelfModel S.X :=
  SelfModelMap.selfModel S.toFiniteTriple

end RelationalStructure

end
