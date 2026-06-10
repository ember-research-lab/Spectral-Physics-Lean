/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom, Claude (Anthropic)
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Fintype.Perm

/-!
# Joint-SAGF: the faithfulness penalty — L1 (global penalty is blind) and L2 (naturality sees)

Companion to `results/ASSESSMENT-faithfulness-coercivity.md` §7. The manuscript's
faithfulness condition (Axiom 3, R∘M = id) has no quantitative penalty form; any
candidate penalty built from the *global* spectral measurement
`M(k) = {Tr g_j(k)}` (def:reconstruction-op) factors through the power-sum
moments. This file machine-checks the two closable layers of the assessment:

* **L1 (the honest negative, CLOSED).** There exist kernels `kC ≠ kS` (not
  gauge-equivalent) with identical global moments: `witness_isospectral` +
  `witness_not_gauge`. Hence every global penalty is constant across them
  (`global_penalty_blind`) — **the global faithfulness penalty is not
  point-separating transverse to gauge, a fortiori not coercive on K_SR/gauge.**
  Witness: the Saltire cospectral pair (C₄ ⊔ K₁ vs the star K_{1,4}; van
  Dam–Haemers, *Which graphs are determined by their spectrum?*), as 0/1
  Hermitian kernels on 5 relational points.

* **L2 (naturality is strictly stronger, CLOSED).** The decomposition-restricted
  (sector) measurement — restricted second moments over 3-point sectors —
  separates the same pair: `naturality_separates`. "Axiom 3(ii) sees what the
  global spectrum cannot" is a checked fact, not prose.

* **L3 (OPEN, T3).** `SectorRigidityProp`: full sector data determines the
  kernel up to monomial gauge (permutation × diagonal units — the automorphisms
  preserving the diagonal algebra; per assessment §5b the physical gauge for
  A_obs = ℂ⊗ℍ⊗𝕆 is the SM inner automorphisms × Aut(X,μ), and the canonical
  sector lattice is the algebra's own). Stated, named, **not used by any
  theorem** (RIGOROUS_WORKFLOW T3 discipline). Its quantitative strengthening
  (coercivity of the sectorwise penalty transverse to gauge × D_F-moduli) is
  assessment §5/§5b.

## Honest scope

Finite model (5-point kernel space, ℤ entries). The five power sums stand in
for the full global moment data: over ℚ they determine the spectrum (Newton's
identities — cited, not formalized here). Gauge in the witness theorems is
permutation conjugation; the separation survives the full monomial gauge since
diagonal units preserve entry absolute values (`witness_not_monomial`). No new
axioms; everything below is `decide`/elementary.
-/

namespace SpectralPhysics.JointSAGF.Faithfulness

open Finset

/-! ### The witness pair (Saltire): C₄ ⊔ K₁ and K_{1,4} as relational kernels -/

/-- Kernel 1: the 4-cycle 0–1–2–3–0 plus the isolated point 4. -/
def kC : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0,1,0,1,0; 1,0,1,0,0; 0,1,0,1,0; 1,0,1,0,0; 0,0,0,0,0]

/-- Kernel 2: the star with center 0 and leaves 1–4. -/
def kS : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0,1,1,1,1; 1,0,0,0,0; 1,0,0,0,0; 1,0,0,0,0; 1,0,0,0,0]

/-! ### L1: the global measurement is blind to the pair -/

/-- The global spectral measurement: the first five power-sum moments
`Tr k, Tr k², …, Tr k⁵` — the finite-model form of def:reconstruction-op's
moment data `{Tr g_j(L)}`. Over ℚ these determine the spectrum (Newton). -/
def specMoments (k : Matrix (Fin 5) (Fin 5) ℤ) : Fin 5 → ℤ :=
  fun m => (k ^ (m.1 + 1)).trace

/-- **L1a.** The witness kernels are isospectral: all five global moments agree
(`[0, 8, 0, 32, 0]` — verified by kernel computation). -/
theorem witness_isospectral : specMoments kC = specMoments kS := by decide

/-- Gauge at the relational level: permutation conjugation (relabeling of the
points of (X, μ)). -/
abbrev GaugeEquiv (a b : Matrix (Fin 5) (Fin 5) ℤ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 5), b = a.submatrix σ σ

/-- **L1b.** The witness kernels are NOT gauge-equivalent (checked over all
120 relabelings). -/
theorem witness_not_gauge : ¬ GaugeEquiv kC kS := by decide +kernel

/-- Full monomial gauge: permutation × diagonal signs (`Bool` encodes ℤˣ; the
transformations preserving the diagonal algebra — for complex kernels,
diagonal phases). -/
abbrev sign (b : Bool) : ℤ := if b then 1 else -1

abbrev MonomialGauge (a b : Matrix (Fin 5) (Fin 5) ℤ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 5)) (d : Fin 5 → Bool),
    b = fun i j => sign (d i) * a (σ i) (σ j) * sign (d j)

/-- **L1b′.** Not monomial-gauge-equivalent either: diagonal units preserve
entry absolute values, and the multiset of row absolute sums differs (the star
has a degree-4 point, the cycle does not). Checked over all 120·2⁵ cases. -/
theorem witness_not_monomial : ¬ MonomialGauge kC kS := by decide +kernel

/-- **L1 headline.** Every global penalty — every functional of the measured
moments, hence every quantitative form of "R∘M = id" built from global
spectral data — takes equal values on the two gauge-inequivalent witnesses.
The global faithfulness penalty is not point-separating transverse to gauge;
a fortiori it is not coercive on K_SR/gauge. (DEGENERATE, closed as an honest
negative.) -/
theorem global_penalty_blind {α : Type*} (F : (Fin 5 → ℤ) → α) :
    F (specMoments kC) = F (specMoments kS) :=
  congrArg F witness_isospectral

/-- Sanity (gauge directions are benign, witness-level): the global moments are
invariant under relabeling — gauge flatness is equivalence, not degeneracy.
Checked over all 120 relabelings of `kC`. -/
theorem specMoments_gauge_invariant_kC :
    ∀ σ : Equiv.Perm (Fin 5), specMoments (kC.submatrix σ σ) = specMoments kC := by
  decide +kernel

/-! ### L2: the sector (naturality) measurement separates the pair -/

/-- Sector measurement: restricted second moments `Tr((k|_S)²)` over all
3-point sectors `S` — the decomposition-restricted data that Axiom 3(ii)
(naturality) demands `R` recover. Collected as a multiset: gauge acts by
permuting sectors, so the multiset is the gauge-covariant datum. -/
def sectorData (k : Matrix (Fin 5) (Fin 5) ℤ) : Multiset ℤ :=
  ((Finset.univ : Finset (Fin 5)).powersetCard 3).val.map
    fun S => ∑ i ∈ S, ∑ j ∈ S, k i j * k j i

/-- **L2 headline.** The sector measurement separates the isospectral pair:
`sectorData kC = {0,0,2,2,2,2,4,4,4,4} ≠ {0,0,0,0,4,4,4,4,4,4} = sectorData kS`.
Naturality (Axiom 3(ii)) is strictly stronger than global faithfulness
(Axiom 3(i) read through moments): it sees structure the global spectrum
cannot. -/
theorem naturality_separates : sectorData kC ≠ sectorData kS := by decide

/-! ### L3: the open problem (named, unused — T3) -/

/-- Sector traces of a kernel: `Tr((k|_S)^m)` for every sector `S ⊆ Fin n`
and power `m`. -/
def sectorTrace {n : ℕ} (k : Matrix (Fin n) (Fin n) ℤ) (S : Finset (Fin n))
    (m : ℕ) : ℤ :=
  ((k.submatrix (fun i : {x // x ∈ S} => i.1) (fun i : {x // x ∈ S} => i.1)) ^ m).trace

/-- Monomial gauge at size `n`. -/
abbrev MonomialGaugeN {n : ℕ} (a b : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (d : Fin n → Bool),
    b = fun i j => sign (d i) * a (σ i) (σ j) * sign (d j)

/-- **OPEN PROBLEM (T3 — not used by any theorem in this repo).**
Sector rigidity: full sector data determines a symmetric kernel up to monomial
gauge. This is quantitative Axiom 3(ii) in its weakest (point-separation) form;
its quantitative strengthening — a coercivity bound for the sectorwise penalty
transverse to gauge × D_F-moduli on Weyl-bounded sets — is the missing premise
of the legibility-vacuum chain (assessment §5, §5b, §6). Known structure: size-1
and size-2 sectors fix the diagonal and entry magnitudes; size-3 sectors fix
sign (phase) triple-products; what remains is exactly the monomial ambiguity —
so the statement is sharp if true. -/
def SectorRigidityProp (n : ℕ) : Prop :=
  ∀ k k' : Matrix (Fin n) (Fin n) ℤ, k.IsSymm → k'.IsSymm →
    (∀ S m, sectorTrace k S m = sectorTrace k' S m) → MonomialGaugeN k k'

end SpectralPhysics.JointSAGF.Faithfulness
