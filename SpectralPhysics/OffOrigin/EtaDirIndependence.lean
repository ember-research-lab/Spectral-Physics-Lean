/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta
import SpectralPhysics.OffOrigin.ForwardOriginSplit
import Mathlib.Data.Matrix.Basic

/-!
# eta_dir independence — Phase 3 scaffold (grounded on the rigorous deficit infra)

Reuses `VisibleSpectrum` / `informationContent` from `SelfModelDeficitRigorous.SpectralZeta`
(the even / M1 deficit `-ζ̃'(0)_vis = Σ mult·(-log y)`), so the blindness lemma below applies
to the framework's actual spectral functional, not a toy.

STATUS (do NOT upgrade without an adversarial audit: vacuity check + `#print axioms`):
- `spectral_functional_M2_invariant`, `informationContent_M2_invariant` : **CLOSED given the
  hypothesis** `frozen` (a pure-M2 deformation fixes the visible eigenvalue spectrum). The
  remaining work is to *derive* `frozen` from non-normal operator theory (numerical range /
  nilpotent-in-eigenbasis) — verdict for that operator-theoretic statement: **OPEN**.
- `forward_origin` : **discharged in-body from `loop_reads_arrow`** (no open hole in its body). The old
  single opaque obligation is split (2026-07 tilt probe): the matrix-level content is CLOSED
  in `OffOrigin/ForwardOriginSplit.lean`, and the residue is the strictly-narrower
  `loop_reads_arrow` (does the physical loop read the `sym ∘ Im` parity-mixing channel?),
  which carries the file's single open obligation. Phase 1 = BACK-SOLVE, Phase 2 = FREE: no
  spectral closure can supply it (it factors through the spectrum → invariant above), and no
  field-of-values closure is known to.

PARITY CORRECTION (2026-06-28, rev. 2026-06-29, off-origin-directed-side/DIRECTED-SIDE-STATUS-2026-06.md):
η_dir's content splits by parity into TWO OPEN pieces. Its MAGNITUDE = the numerical abscissa
ω = λ_max(symmetricPart G) reads symmetricPart(L_κ) = L + κ·B_sym, which MOVES WITH κ (the one-way
coupling's symmetric part B_sym ≠ 0); it escapes the EIGENVALUE blindness theorem (field-of-values,
not eigenvalue) but for that reason is DIRECTED content, located by a back-solve (κ_crit ∝ Λ),
OPEN at Tier 2 — NOT κ-independent derivable geometry. (Corrects an earlier note that called it
"derivable geometry": symmetricPart(L_κ) depends on κ, so being read by ω ≠ being origin-geometry.)
The genuinely-external, irreducible content `forward_origin` is about is the residual ANTISYMMETRIC
ORIENTATION ℤ/2 (the L/R eigenframe orientation = transpose), invisible to every transpose-invariant functional
(the whole framework inventory; see triple_invariant_M2_invariant). It needs a non-spectral source —
the Pfaffian sign Pf(Aᵀ)=(−1)ⁿPf(A) or a Krein signature — none formalized here yet. So the sharp
form of `ForwardOriginExists` is "a ℤ/2-valued non-spectral selector (Pfaffian/Krein)", stronger than
the generic real selector `NonSpectral` below; tightening it is future work.
-/

namespace SpectralPhysics.OffOrigin

open SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta

/-- A pure-M2 deformation: a κ-family of visible spectra whose eigenvalue data is held fixed
(the directed/eigenvector geometry varies off-spectrum). That M2 deformations have this
spectrum-freezing property is the modelling input (*Part: Off-Origin*; confirmed numerically in
`output/closure_probe.md`, where the joint heat trace is constant in κ). -/
structure M2Deformation where
  spec : ℝ → VisibleSpectrum
  frozen : ∀ κ κ', spec κ = spec κ'

/-- **Blindness of the closure (provable core).** Any spectral functional — anything that
factors through the visible spectrum — is constant along a pure-M2 deformation. So no spectral
closure (heat trace, SCSE `Γ(ζ_D)=ζ_D`, SAGF) has a gradient on the M2 axis. -/
theorem spectral_functional_M2_invariant
    (F : VisibleSpectrum → ℝ) (D : M2Deformation) (κ κ' : ℝ) :
    F (D.spec κ) = F (D.spec κ') := by
  rw [D.frozen κ κ']

/-- Corollary for the framework's even (M1) deficit: it cannot move along the directed axis. -/
theorem informationContent_M2_invariant (D : M2Deformation) (κ κ' : ℝ) :
    informationContent (D.spec κ) = informationContent (D.spec κ') :=
  spectral_functional_M2_invariant informationContent D κ κ'

/-- A selector of `eta_dir`. **Non-spectral** = it distinguishes deformations that share a
(frozen) spectrum, i.e. is not determined by the eigenvalue data (necessary for any forward
origin, by the invariance above). -/
def NonSpectral (sel : M2Deformation → ℝ) : Prop :=
  ∃ D D' : M2Deformation, (∀ κ κ', D.spec κ = D'.spec κ') ∧ sel D ≠ sel D'

/-- **OPEN.** A forward, observable-free origin for `eta_dir`: a non-spectral selector exists.
(The full statement adds framework-distinguishedness + uniqueness; even this weaker existence is
not established — Phases 1–2 give only negative evidence.) -/
def ForwardOriginExists : Prop := ∃ sel : M2Deformation → ℝ, NonSpectral sel

/-! ### The forward-origin split (2026-07, tilt-probe result)

`forward_origin` is no longer one opaque open hole. The tractable, matrix-level content
— that the well-degeneracy holds for every transpose-covariant read, and that the ONE
`sym ∘ Im` parity-mixing channel escapes it and induces a genuine tilt — is CLOSED in
`OffOrigin/ForwardOriginSplit.lean` (`degeneracy_under_oddness`,
`tc_read_tc_kernel_odd_drift`, `symImRead_not_transposeCovariant`, `tilt_source_exists`).

What remains is strictly narrower than the bare `ForwardOriginExists`: not "some
non-spectral selector exists", but "the physical autopoietic loop's selector is the
one produced by the `sym ∘ Im` parity-mixing read of its own complex kernel". That is
`LoopReadsArrow` below — the single remaining open obligation. -/

/-- `sel` is a **`sym ∘ Im` tilt selector**: it factors through the parity-mixing read
`symImRead` (= `sym ∘ Im`) of a complex kernel assigned to each deformation. NAMES the
specific channel the tilt probe located; this is what makes `LoopReadsArrow` strictly
stronger than the generic `NonSpectral`/`ForwardOriginExists`. -/
def IsSymImTilt (sel : M2Deformation → ℝ) : Prop :=
  ∃ assignK : M2Deformation → Matrix (Fin 2) (Fin 2) ℂ,
    ∀ D, sel D = inducedDrift (symImRead (assignK D)) 1

/-- **The narrowed obligation `LoopReadsArrow`.** The physical loop's forward-origin
selector both (a) is non-spectral (`NonSpectral`, necessary by the C1/C2 blindness
theorems) AND (b) is realized by the `sym ∘ Im` parity-mixing read (`IsSymImTilt`).
Strictly stronger than `ForwardOriginExists = ∃ sel, NonSpectral sel`: it additionally
pins the read channel. This is where the residual externality now lives. -/
def LoopReadsArrow : Prop :=
  ∃ sel : M2Deformation → ℝ, NonSpectral sel ∧ IsSymImTilt sel

/-- **The reduction, with no open hole.** If the loop reads the `sym ∘ Im` arrow, a
forward origin exists: the tilt selector is itself the non-spectral selector (drop the
channel-identification conjunct). This is the honest content of the split — a genuine
implication, not a relabel. -/
theorem loop_reads_arrow_implies_forward_origin (h : LoopReadsArrow) :
    ForwardOriginExists :=
  let ⟨sel, hns, _⟩ := h
  ⟨sel, hns⟩

/-- **The one remaining obligation** (the genuinely-open residue, sharper than the old
`forward_origin` gap): that the physical autopoietic loop's selector is the
`sym ∘ Im` tilt. Whether this holds is the upstream question the tilt probe SHARPENS
but does not answer. Carries the single open obligation of this file. -/
theorem loop_reads_arrow : LoopReadsArrow := by
  sorry -- OPEN (narrowed): does the physical loop read `sym ∘ Im` of its own kernel?

/-- `forward_origin` is discharged in its body FROM `loop_reads_arrow` (no open hole in the body) via
the reduction above. The only open obligation in the file is `loop_reads_arrow`. -/
theorem forward_origin : ForwardOriginExists :=
  loop_reads_arrow_implies_forward_origin loop_reads_arrow

/-! ## C2 — M2-blindness of spectral-triple invariants (extends C1 above)

C1 (`spectral_functional_M2_invariant`) covered functionals factoring through the *spectrum*.
C2 extends this to the whole **self-adjoint layer**: a pure-M2 deformation of the dynamical
generator adds an ANTISYMMETRIC `κ • A` (def:Lk, `Aᵀ = -A`), whose symmetric part vanishes, so
the symmetric (self-adjoint) part `D_M`/`L` is unchanged. Every spectral-triple invariant — the
spectral action `Tr f(D/Λ)`, the KO-dimension signs, the K-homology class, the **Connes distance**
`d_D(φ,ψ)=sup{|φ(a)-ψ(a)| : ‖[D,a]‖≤1}` (a witness invariant that is NOT a function of `spec(L)`
alone), and the gauge group `Aut(A)` — factors through this self-adjoint part, hence is M2-blind.

Scope: this is irreducibility to spectral-**triple** invariants (C2), NOT to arbitrary
dynamical/pseudospectral closures (C3), which remains open. -/
section TripleBlindness
open Matrix
variable {n : Type*}

/-- Symmetric (self-adjoint) part of a real square matrix. The spectral triple is built from the
self-adjoint Dirac `D_M` and so sees only this part of the dynamical generator. -/
noncomputable def symmetricPart (M : Matrix n n ℝ) : Matrix n n ℝ := (2:ℝ)⁻¹ • (M + Mᵀ)

/-- A pure-M2 deformation adds an antisymmetric `κ • A` to the generator; its symmetric part is
unchanged. The antisymmetry hypothesis `Aᵀ = -A` is load-bearing: drop it and `κ • A`
contributes `κ • symmetricPart A ≠ 0`, breaking the identity. -/
theorem symmetricPart_add_antisymm (L A : Matrix n n ℝ) (hA : Aᵀ = -A) (κ : ℝ) :
    symmetricPart (L + κ • A) = symmetricPart L := by
  unfold symmetricPart
  rw [transpose_add, transpose_smul, hA, smul_neg]
  congr 1
  abel

/-- **C2 — M2-blindness of spectral-triple invariants.** Any functional `Φ` of the symmetric
(self-adjoint) part — i.e. any spectral-triple invariant — is invariant under a pure-M2
deformation `L ↦ L + κ • A` with `Aᵀ = -A`. Extends `spectral_functional_M2_invariant` from
functions of the spectrum to functions of the whole self-adjoint layer. Hence `η_dir` (the
field-of-values asymmetry, living in the antisymmetric `κ • A`) is transversal to every triple
invariant. -/
theorem triple_invariant_M2_invariant (Φ : Matrix n n ℝ → ℝ) (L A : Matrix n n ℝ)
    (hA : Aᵀ = -A) (κ κ' : ℝ) :
    Φ (symmetricPart (L + κ • A)) = Φ (symmetricPart (L + κ' • A)) := by
  rw [symmetricPart_add_antisymm L A hA, symmetricPart_add_antisymm L A hA]

end TripleBlindness

end SpectralPhysics.OffOrigin
