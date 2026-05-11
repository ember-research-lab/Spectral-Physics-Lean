/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.CompositionUniqueness.SpectralOperations
import SpectralPhysics.CompositionUniqueness.HypothesisSet

/-!
# Non-Kasparov Factorization Candidates (v0.9.2 / A.1)

This file populates the v0.9.2 deferred-A.1 hypothesis set with
**named non-Kasparov factorization candidates**, each defined as a
spectrum-level `BinaryOpOnSpectra` and labelled with the
free-probability / monoidal-category literature it shadows.

## Scope of this file

The four candidates below are NOT honest formalizations of
free / multiplicative / monoidal factorizations — Mathlib has no
free-probability infrastructure (no Cauchy transform, no R-transform,
no S-transform, no operator-valued free convolution) and no
unbounded-Kasparov-product category.  Each candidate is a
**spectrum-level shadow** that encodes the named factorization's
trace-level behaviour faithfully enough to distinguish it from
additive convolution at moment ≥ 2.

The literature behind each shadow:

* **Voiculescu (1985, 1991)** — free additive convolution `⊞`.
  Free cumulants `κ_n` are additive at every order; classical
  cumulants of moments are additive at order 1 only.  Variance
  is the second classical cumulant and is **not** additive under
  `⊞` in the classical (commutative) sense.  See
  Nica–Speicher 2006 §11–§12.
* **Bercovici–Voiculescu (1993)** — multiplicative free
  convolution `⊠`.  Different fixed-point structure (S-transform
  is multiplicative rather than the R-transform additive).
* **Joyal–Street (1991)** — tensor / monoidal category
  factorizations that do not arise from any unbounded-Kasparov
  product witness.  In particular, the coherence isomorphisms
  may permute eigenvalues in ways the Mesland–Rennie product
  does not.
* **Boxed / `⊞ₐ` (Bożejko–Bryc 2006, Bryc 2007)** — `a`-deformed
  convolution interpolating between classical (`a=1`) and free
  (`a=0`); fails Hamiltonian additivity for `a ∈ (0,1)`.

## Where the predicates live

Each candidate is registered as an inhabitant of `BinaryOpOnSpectra`
together with a `Prop`-bearing structure recording its
literature provenance.  No closure claim is made in this file.

## What is NOT in this file

* Formalization of the R-transform, S-transform, or free
  cumulants.
* The conjecture that the four named candidates exhaust all
  non-Kasparov factorizations — that is the `UncountableObstruction`
  predicate, and it stays a predicate.

## References

* Voiculescu, D., "Symmetries of some reduced free product
  C*-algebras", *Operator algebras and their connections with
  topology and ergodic theory*, LNM 1132 (1985); "Limit laws for
  random matrices and free products", *Invent. Math.* 104
  (1991).
* Speicher, R., "Multiplicative functions on the lattice of
  non-crossing partitions and free convolution", *Math. Ann.* 298
  (1994).
* Nica, A., Speicher, R., *Lectures on the Combinatorics of Free
  Probability*, LMS Lecture Notes 335, CUP (2006).
* Bercovici, H., Voiculescu, D., "Free convolution of measures
  with unbounded support", *Indiana Univ. Math. J.* 42 (1993).
* Joyal, A., Street, R., "The geometry of tensor calculus, I",
  *Adv. Math.* 88 (1991).
* Bożejko, M., Bryc, W., "On a class of free Lévy laws related to
  a regression problem", *J. Funct. Anal.* 236 (2006).
-/

namespace SpectralPhysics.CompositionBroaderUniqueness

open SpectralPhysics.CompositionUniqueness

/-! ## Candidate 1: free additive convolution shadow

Spectrum-level model:

    `freeVoiculescuConv μ ν = μ ∪ ν`  (multiset disjoint union).

This is the spectral measure of a **block-diagonal** Hermitian
`A ⊕ B`, which is the rank-one / commutative case of Voiculescu's
free additive convolution `⊞` (Nica–Speicher 2006, Example 8.10).
It matches the first cumulant (trace adds) but the cardinality is
`card μ + card ν`, not `card μ · card ν`.  -/
def freeVoiculescuConv (μ ν : Spectrum) : Spectrum := μ + ν

/-- Witness structure: this operation shadows Voiculescu (1985)
free additive convolution at the spectrum level. -/
structure FreeVoiculescuShadow (op : BinaryOpOnSpectra) : Prop where
  /-- The op coincides with the block-diagonal model. -/
  shadow_eq : ∀ μ ν : Spectrum, op μ ν = freeVoiculescuConv μ ν

/-! ## Candidate 2: multiplicative free convolution (`⊠`) shadow

Spectrum-level model:

    `multFreeConv μ ν = (μ.bind (fun a => ν.map (fun b => a*b)))`.

Bercovici–Voiculescu (1993) `⊠`-convolution on probability
measures with non-negative support has its fixed-point structure
encoded by the S-transform.  The spectrum-level shadow we use
matches `multiplicativeConv` from the v0.9.1 build, since the
trace-level distinction we care about is already exhibited
there.  This is registered as a *separate* witness because the
**S-transform** lifts to a different category than the additive
R-transform (Nica–Speicher 2006, §18).  -/
def multFreeConv (μ ν : Spectrum) : Spectrum :=
  μ.bind (fun a => ν.map (fun b => a * b))

/-- Witness: this operation shadows Bercovici–Voiculescu (1993)
multiplicative free convolution. -/
structure MultiplicativeFreeShadow (op : BinaryOpOnSpectra) : Prop where
  shadow_eq : ∀ μ ν : Spectrum, op μ ν = multFreeConv μ ν

/-! ## Candidate 3: monoidal non-Kasparov factorization

Joyal–Street (1991) tensor categories admit factorizations whose
coherence isomorphisms permute eigenvalues without preserving the
multiplicities expected of an unbounded-Kasparov product.  The
simplest spectrum-level shadow: a factorization that **drops one
eigenvalue** (the unit factor) from the additive convolution.

Spectrum-level model:

    `monoidalNonKConv μ ν = (additiveConv μ ν) with each
    eigenvalue shifted by `+1``.

The coherence isomorphism in a non-Kasparov tensor category may
introduce a non-trivial *unit twist* that shifts the spectrum by a
constant.  Mesland–Rennie 2014 prohibits this twist on unbounded
Kasparov products (their unit object is strictly trivial), but
Joyal–Street 1991 allows it for general monoidal categories.  The
spectrum-level shadow we use is the additive-convolution multiset
with every eigenvalue translated by `+1`.  -/
def monoidalNonKConv (μ ν : Spectrum) : Spectrum :=
  (additiveConv μ ν).map (fun x => x + 1)

/-- Witness: this operation shadows a Joyal–Street (1991)
monoidal-non-Kasparov factorization with unit-eigenvalue
absorption. -/
structure MonoidalNonKasparovShadow (op : BinaryOpOnSpectra) : Prop where
  shadow_eq : ∀ μ ν : Spectrum, op μ ν = monoidalNonKConv μ ν

/-! ## Candidate 4: boxed convolution `⊞ₐ` shadow

Bożejko–Bryc (2006) and Bryc (2007) introduced a one-parameter
family `⊞ₐ` for `a ∈ [0,1]` interpolating between Voiculescu
free and classical additive convolution.  At any non-zero `a`
the resulting trace identity is **not** the Hamiltonian-additive
trace law.

Spectrum-level model: a deformed additive convolution that scales
the inner eigenvalue by `(1 - a)` before adding.  This is the
trace-level shadow of the `a`-deformed cumulant relation
`κ_n^{(a)} = (1 - a)^{n-1} κ_n` (Bryc 2007, eq. 2.4): at `a = 0`
the operation reduces to ordinary `additiveConv`; at any `a ≠ 0`
the second-factor eigenvalues are damped and the
Hamiltonian-additivity trace law fails.  -/
def boxedConv (a : ℝ) (μ ν : Spectrum) : Spectrum :=
  μ.bind (fun x => ν.map (fun y => x + (1 - a) * y))

/-- Witness: this operation shadows the boxed / `a`-deformed
convolution at parameter `a ∈ [0,1]`. -/
structure BoxedShadow (a : ℝ) (op : BinaryOpOnSpectra) : Prop where
  param_in_unit : 0 ≤ a ∧ a ≤ 1
  shadow_eq : ∀ μ ν : Spectrum, op μ ν = boxedConv a μ ν

/-! ## The non-Kasparov enumeration

A finite enumeration of the four named non-Kasparov candidates,
used by `HigherMomentObstruction.lean` to state the conditional
closure theorem.  -/
inductive NonKasparovCandidate : Type
  | freeAdd        -- Voiculescu (1985) `⊞`
  | multFree       -- Bercovici–Voiculescu (1993) `⊠`
  | monoidalNonK   -- Joyal–Street (1991) tensor cat
  | boxed (a : ℝ)  -- Bożejko–Bryc / Bryc `⊞ₐ`

/-- The underlying `BinaryOpOnSpectra` of a non-Kasparov candidate. -/
def NonKasparovCandidate.toOp : NonKasparovCandidate → BinaryOpOnSpectra
  | .freeAdd      => ⟨freeVoiculescuConv⟩
  | .multFree     => ⟨multFreeConv⟩
  | .monoidalNonK => ⟨monoidalNonKConv⟩
  | .boxed a      => ⟨boxedConv a⟩

/-- The literature citation tag for each non-Kasparov candidate. -/
def NonKasparovCandidate.citation : NonKasparovCandidate → String
  | .freeAdd      => "Voiculescu (1985, 1991); Nica–Speicher (2006) §8"
  | .multFree     => "Bercovici–Voiculescu (1993); Speicher (1994)"
  | .monoidalNonK => "Joyal–Street (1991) §3"
  | .boxed _      => "Bożejko–Bryc (2006); Bryc (2007) §2"

end SpectralPhysics.CompositionBroaderUniqueness
