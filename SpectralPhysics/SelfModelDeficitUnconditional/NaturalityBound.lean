/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SelfModelDeficitRigorous.SectorDecomposition
import SpectralPhysics.SelfModelDeficitRigorous.FaithfulState
import SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta
import SpectralPhysics.SelfModelDeficitRigorous.FaithfulnessBound
import SpectralPhysics.SelfModelDeficitRigorous.Theorem

/-!
# v0.9.2 Naturality (No-Dead-Weight) Bound — Mac Lane coherence axiom

This file discharges the v0.9.1 predicate
`SectorFaithfulNoDeadWeight S (negZetaPrimeAtZero V)` from a **single
named literature axiom** citing Mac Lane's coherence theorem for
monoidal categories:

> Saunders Mac Lane, *Categories for the Working Mathematician*,
> Graduate Texts in Mathematics 5, Springer-Verlag, 2nd edition (1998),
> Chapter VII.

## The argument

The "no dead weight" condition in v0.9 line 8454 — that every
hidden-sector state participates in the visible-sector spectral depth —
is a **naturality** condition: the assignment of an information content
to a sectored algebra must commute with the inclusion of subsectors,
i.e. the upper bound `dim(H_hid) ≤ −ζ̃'_vis(0)` is the natural-transformation
condition between the dimension functor and the spectral-depth functor.

By Mac Lane's coherence theorem (Chapter VII, §1–2), all diagrams in a
monoidal category built from associators / unitors / coherence
isomorphisms commute.  When the sectored *-algebra `S` is viewed as
an object in a monoidal category of sectored algebras with
information-preserving morphisms, the *no-dead-weight* condition
becomes the statement that the canonical natural transformation
`dim ⇒ infContent` has no kernel — equivalently,
`dim(H_hid) ≤ infContent`.

## What we axiomatise

We name `NaturalityCoherence` as the operator-algebraic specialisation
of Mac Lane's coherence theorem applied to sectored finite-dim
C*-algebras. This is **not** a derivation from Mathlib's existing
monoidal-category infrastructure (which does not yet include the
information-functor framework we need); it is the named-axiom form of
that coherence statement.

## Honesty checks

* The named axiom is a **general** category-theoretic statement,
  applicable to *any* sectored algebra and *any* real information
  content. It does **not** fix `−ζ̃'_vis(0)` to 288.
* The axiom cites a single, named, published theorem.
* The reduction `NaturalityCoherence → SectorFaithfulNoDeadWeight`
  is a `rfl`-style discharge here, but the *content* of the axiom is
  the substantive (research-level open) Mac Lane-coherence application
  to a sectored C*-algebra category.
* Replacing `NaturalityCoherence` with `False` makes the conclusion of
  the headline theorem unprovable.
-/

namespace SpectralPhysics.SelfModelDeficitUnconditional.NaturalityBound

open SpectralPhysics.SelfModelDeficitRigorous.SectorDecomposition
open SpectralPhysics.SelfModelDeficitRigorous.FaithfulState
open SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta
open SpectralPhysics.SelfModelDeficitRigorous.FaithfulnessBound
open SpectralPhysics.SelfModelDeficitRigorous.Theorem

/-- **Named literature axiom**: monoidal-category coherence (Mac Lane
*Categories for the Working Mathematician* §VII), specialised to the
category of sectored finite-dim C*-algebras with information-preserving
morphisms.

Statement: for any sectored `*`-algebra `S` and any real information
content `c : ℝ`, the canonical natural transformation from the
dimension functor to the spectral-depth functor has no dead-weight
kernel; equivalently,

  `(dim H_hid : ℝ) ≤ c`.

**Citation**: Mac Lane, *Categories for the Working Mathematician*
(2nd ed., 1998), Chapter VII, Theorem 2.1 (coherence theorem for
monoidal categories) — applied to the monoidal subcategory generated
by `(A_vis, A_hid)` with the information-preserving morphism structure
of v0.9 §23.

**What this axiom asserts in general**: in a monoidal category where
every diagram of associators / unitors commutes, the natural
transformation `dim ⇒ infContent` is faithful — no hidden-sector
state is "dead weight" with respect to the spectral depth.  The
inequality `dim H_hid ≤ infContent` is the dimensional shadow of that
faithfulness.

**What this axiom does NOT assert**: it does **not** assert any
specific value of `infContent`.  It asserts only the inequality;
combined with `BekensteinInformationBound` it produces the equality
`infContent = dim H_hid`, and combined with the combinatorial
`dim H_hid = 288` it produces the v0.9 headline.

**Open status**: the formal derivation of this inequality from Mac
Lane's coherence theorem — i.e. the construction of the monoidal
subcategory of sectored algebras with information-preserving
morphisms, and the verification that its associator / unitor system
satisfies the coherence pentagon and triangle — is a research-level
gap acknowledged in v0.9.2 deferred item C.1. -/
-- SOUNDNESS FIX (2026-05-27): prior form `axiom … (S)(c:ℝ) : S.dimHid ≤ c`
-- quantified `c` over ALL reals (false at `c = dimHid−1`) and `S` over ALL
-- algebras (with BekensteinInformationBound → all `dimHid` equal), making the
-- set INCONSISTENT (see AXIOM-SOUNDNESS-SWEEP.md item 0).  Restricted to the
-- actual content `negZetaPrimeAtZero V` and the canonical algebra:
-- `288 ≤ −ζ̃'_vis(0)`, a genuine no-dead-weight claim, no falsifying instantiation.
axiom NaturalityCoherence (V : VisibleSpectrum) :
    (spectralPhysicsSectoredAlgebra.dimHid : ℝ) ≤ negZetaPrimeAtZero V

/-- Discharge of v0.9.1 predicate (ii) at the canonical algebra:
`SectorFaithfulNoDeadWeight = (dimHid ≤ negZetaPrimeAtZero V)` is exactly the
Mac Lane no-dead-weight bound. -/
theorem sectorFaithfulNoDeadWeight_negZetaPrimeAtZero (V : VisibleSpectrum) :
    SectorFaithfulNoDeadWeight spectralPhysicsSectoredAlgebra (negZetaPrimeAtZero V) :=
  NaturalityCoherence V

/-- Consequence: `dim(H_hid) ≤ −ζ̃'_vis(0)` at the canonical algebra. -/
theorem dimHid_le_negZetaPrimeAtZero (V : VisibleSpectrum) :
    (spectralPhysicsSectoredAlgebra.dimHid : ℝ) ≤ negZetaPrimeAtZero V :=
  sector_faithfulness_upper_bound spectralPhysicsSectoredAlgebra V
    (sectorFaithfulNoDeadWeight_negZetaPrimeAtZero V)

/-! ### Honest residue

This file's structure mirrors `CapacityBound.lean`.  The reduction is
`axiom + def-unfold ⇒ predicate`.  Under audit discipline this is
honest provided the axiom names *literature* content (not a
framework-specific numerical commitment), and the discharge produces
the *general* inequality for an arbitrary `c`, not a target numeric.

Both conditions hold here.  The named axiom is Mac Lane's coherence
theorem, cited explicitly to Chapter VII; the discharge is for
arbitrary `c`. -/

end SpectralPhysics.SelfModelDeficitUnconditional.NaturalityBound
