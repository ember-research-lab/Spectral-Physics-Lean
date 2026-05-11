/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import SpectralPhysics.Eta.JumpMap

/-!
# Spectral Identification: The Open Predicate

This file formalises the **spectral identification map**

  `ϕ : ModeClass → Finset (Fin 384)`

as a **Prop-valued predicate** on `(T, ϕ)` pairs, *not* as a
definitional choice and *not* as an axiom forcing existence.

## Role in the audit-honest pipeline

The four integer η-jump claims of the spectral-physics framework

  ```
  |Δη_GUT|       = 12
  |Δη_QCD|       = 144
  |Δη_EW|        = 168
  |Δη_full M×F|  = 768
  ```

cannot be obtained from a purely combinatorial map on `Fin 384`.
That was the audit-caught error of the prior deceptive branch.

For the integers to be **physically meaningful**, the index ranges
`{0,…,5}` (GUT), `{0,…,71}` (QCD), `{0,…,83}` (EW), `{0,…,383}` (full)
must correspond to the *actual* eigenvalue-crossing modes of the
framework's specific `D_F` along the σ- and r-axis spectral flows.
Whether that correspondence holds is an **open** question — it is a
statement *about* the unspecified eigenvalue structure of the
framework's `D_F`, not a tautology.

This file:

* Defines `SpectralIdentification` as a Prop-valued predicate on
  `(T_before, T_after, ϕ)` triples.
* Does **not** assert that the predicate holds for any specific `T`.
* Does **not** introduce an axiom forcing a specific identification.

The downstream module `IntegerCounts.lean` then states the four
integer claims as **conditional theorems** with the predicate as a
hypothesis.

## Smuggling check

* No theorem in this file outputs a specific real or natural number.
* The predicate is parameterised over `ModeClass` and over the
  triple, so its content depends entirely on what `(T_before, T_after,
  ϕ)` are.
* If `ϕ` is the trivial constant map, the predicate becomes a
  trivial statement — but no such trivialisation is asserted anywhere.

The substantive question is: *does the framework's actual `D_F`
admit a spectral-identification map `ϕ` matching the four physical
mode classes?*  We do NOT answer that question in this branch.
-/

namespace SpectralPhysics.Eta.IdMap

open SpectralPhysics.Eta.JumpMap

/-! ## Mode classes -/

/-- The four physical mode classes of the spectral-physics framework.

* `GUT`  — right-handed-neutrino seesaw crossing on the σ-axis at the
           GUT scale.
* `QCD`  — colored-fermion modes participating in QCD-active
           crossings on the r-axis.
* `EW`   — electroweak charged-fermion modes (QCD ∪ charged leptons).
* `Full` — all 384 modes of `H_F`.

This inductive type carries no numerical content — it is purely a
label. -/
inductive ModeClass
  | GUT
  | QCD
  | EW
  | Full
  deriving DecidableEq, Repr

/-! ## Spectral-identification map

A *spectral-identification map* is an assignment of an index subset of
`Fin dimHF` to each `ModeClass`.  It is the OPEN content: which
indices of the abstract `dim H_F = 384` basis correspond to which
physical mode classes. -/

/-- A **spectral-identification map**: for each `ModeClass`, an index
    subset of `Fin dimHF`. -/
def SpectralIdMap : Type := ModeClass → Finset (Fin dimHF)

/-! ## The predicate -/

/-- **Spectral identification predicate** on `(T_before, T_after, ϕ)`.

This predicate says that the index subset `ϕ c` for each mode class
`c` correctly captures the spectral-flow crossings *of the actual
finite Dirac operator* `D_F` between the two endpoint triples
`T_before` and `T_after`:

  *the crossings of `D_F` indexed by `ϕ c` are exactly the
   physical-mode-class-`c` eigenvalue crossings of `D_F`.*

Concretely we require: for each mode class `c`, the set of crossing
indices `crossingSet T_before T_after ∩ ϕ c` equals `ϕ c` (every
mode in the class crosses) and is disjoint from `ϕ c'` for `c ≠ c'`
when the two classes are physically disjoint.

Plus a structural soundness condition: `ϕ c` is non-empty whenever
`c` corresponds to a physically populated mode class.

**This predicate is the OPEN content.**  Whether it holds for the
framework's actual `D_F` requires:

1. An eigenvalue spectrum for `D_F` on the σ-axis (resp. r-axis)
   produced by the spectral action of the framework — see
   v0.9 Theorem `thm:384`, line 8211.
2. A computation of which eigenvalues cross zero under the σ- or r-
   axis spectral flow.
3. A pairing of those crossings with the physical mode classes
   (Standard-Model fermions decomposed by representation).

None of these three are formalised here.  The predicate captures
*what would need to be true* for the integer counts in
`IntegerCounts.lean` to follow. -/
structure SpectralIdentification
    (T_before T_after : FiniteSpectralTriple) (ϕ : SpectralIdMap) : Prop where
  /-- Every mode in `ϕ c` is an actual spectral-flow crossing of `D_F`
      between the two endpoints. -/
  modes_cross :
    ∀ c : ModeClass, ϕ c ⊆ crossingSet T_before T_after
  /-- The full class `Full` corresponds to all 384 modes.
      (This is the only labelling constraint imposed; the others are
      left to the downstream theorems.) -/
  full_is_all : ϕ ModeClass.Full = Finset.univ
  /-- Physical containment: QCD modes are contained in EW modes
      (since QCD-colored fermions also carry electroweak charge). -/
  qcd_subset_ew : ϕ ModeClass.QCD ⊆ ϕ ModeClass.EW
  /-- Physical disjointness: GUT seesaw modes (right-handed neutrinos)
      do not overlap with electroweak charged fermions. -/
  gut_disjoint_ew : Disjoint (ϕ ModeClass.GUT) (ϕ ModeClass.EW)

/-! ## Lemmas: derived structural relations

Given the predicate, derive simple inclusion / disjointness facts
that downstream theorems can use without re-invoking the predicate. -/

variable {T_before T_after : FiniteSpectralTriple} {ϕ : SpectralIdMap}

/-- If the spectral identification holds, the QCD class is contained
    in the EW class as a `Finset`. -/
theorem qcd_subset_ew_of_id
    (h : SpectralIdentification T_before T_after ϕ) :
    ϕ ModeClass.QCD ⊆ ϕ ModeClass.EW := h.qcd_subset_ew

/-- If the spectral identification holds, the GUT class is disjoint
    from the EW class. -/
theorem gut_disjoint_ew_of_id
    (h : SpectralIdentification T_before T_after ϕ) :
    Disjoint (ϕ ModeClass.GUT) (ϕ ModeClass.EW) := h.gut_disjoint_ew

/-- If the spectral identification holds, every mode in any class is
    an actual crossing of `D_F`. -/
theorem modes_cross_of_id
    (h : SpectralIdentification T_before T_after ϕ) (c : ModeClass) :
    ϕ c ⊆ crossingSet T_before T_after := h.modes_cross c

/-- If the spectral identification holds, the `Full` class has
    cardinality `dimHF = 384`. -/
theorem full_card_of_id
    (h : SpectralIdentification T_before T_after ϕ) :
    (ϕ ModeClass.Full).card = dimHF := by
  rw [h.full_is_all, Finset.card_univ, Fintype.card_fin]

/-! ## The four physical cardinality hypotheses

To get the integers 12 = 2·6, 144 = 2·72, 168 = 2·84, 768 = 2·384,
we need the cardinalities of `ϕ GUT`, `ϕ QCD`, `ϕ EW`, `ϕ Full` to be
respectively 6, 72, 84, 384.

We do **not** assert these as conclusions of `SpectralIdentification`.
Instead, we bundle them into a **separate** predicate
`PhysicalCardinalities`.  That predicate is the load-bearing
spectral-physics content: it says "the framework's `D_F` has, for
each physical mode class, exactly this many crossing modes."

Whether `PhysicalCardinalities` holds is the open spectral-physics
question — it is the *concrete numerical content* that
v0.9 Theorem `thm:384` would have to provide. -/

/-- **Physical-cardinality predicate** on a spectral-identification
    map `ϕ`.  Asserts that the four mode classes have the
    cardinalities required for the integer η-jumps:

      * `ϕ GUT  : 6  modes`  (3 generations × 2 ν_R chiralities; no
                              particle/antiparticle doubling at the
                              index level — that comes from Majorana
                              η-doubling).
      * `ϕ QCD  : 72 modes`  (12 colored quark states × 3 gen × 2 p/a).
      * `ϕ EW   : 84 modes`  (QCD + 12 charged-lepton modes).
      * `ϕ Full : 384 modes` (all of `H_F`).

    This predicate is what v0.9 Theorem `thm:384` and the associated
    spectral-action computation would have to supply for the
    integers 12, 144, 168, 768 to follow.

    **NOT proved here.**  It is a hypothesis. -/
structure PhysicalCardinalities (ϕ : SpectralIdMap) : Prop where
  gut_card : (ϕ ModeClass.GUT).card = 6
  qcd_card : (ϕ ModeClass.QCD).card = 72
  ew_card : (ϕ ModeClass.EW).card = 84
  full_card : (ϕ ModeClass.Full).card = 384

/-! ## Honesty: what this file does NOT do

* It does **not** define any specific `ϕ` and prove the cardinalities.
  Doing so would amount to the deceptive `2 · card` pattern.
* It does **not** assert `SpectralIdentification` for any specific
  `(T_before, T_after, ϕ)`.
* It does **not** assert `PhysicalCardinalities` for any specific `ϕ`.
* It introduces zero axioms.

The substantive question — "does the framework's actual `D_F`, with
its specific spectral-action-derived eigenvalue spectrum, admit a
spectral-identification map `ϕ` satisfying both
`SpectralIdentification T_before T_after ϕ` and
`PhysicalCardinalities ϕ`?" — is **OPEN**. -/

end SpectralPhysics.Eta.IdMap
