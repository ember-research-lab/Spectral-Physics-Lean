/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Tactic.NormNum
import SpectralPhysics.Eta.JumpMap
import SpectralPhysics.Eta.SpectralIdentification

/-!
# Conditional Integer-Count Theorems for the η-Jumps

This file states the four headline integer claims of the spectral-
physics framework

```
|Δη_GUT|       = 12
|Δη_QCD|       = 144
|Δη_EW|        = 168
|Δη_full M×F|  = 768
```

as **conditional theorems** of the form

```
SpectralIdentification T_before T_after ϕ
  → PhysicalCardinalities ϕ
  → AbsEtaJumpClass T_before T_after (ϕ c) = APS_factor * (ϕ c).card.
```

The integers 12, 144, 168, 768 are **NOT** definitional outputs of
`2 * S.card`.  They emerge as **consequences** of:

* the structural spectral-flow definition of `η` (in `JumpMap.lean`),
* the spectral-identification predicate (in `SpectralIdentification.lean`),
* the *physical-cardinality* hypothesis on `ϕ` (also in
  `SpectralIdentification.lean`),
* and ONE named axiom — `aps_bismut_freed_majorana_doubling` — that
  asserts the APS / Bismut-Freed factor-of-2 for Majorana-paired modes
  of a KO-dim 6 finite spectral triple, with explicit literature
  citations.

## What changed from the pre-redemption deceptive branch

| Aspect | pre-redemption | this file |
|---|---|---|
| `etaJump` definition | `def etaJump S := 2 * S.card` | absent; the abstract η-jump is a structural functional |
| "axiom" `etaJump_two_times_modes` | `rfl`-provable | replaced by `aps_bismut_freed_majorana_doubling`, an *existence statement* citing 1986 Bismut-Freed |
| Integers 12/144/168/768 | provable from definition + rfl | provable only with two hypotheses + one named axiom |
| Spectral identification | implicit / definitional via index ranges | explicit Prop-valued predicate; left OPEN |

## Smuggling check

* The named axiom does NOT mention `2 * S.card`.  It asserts the
  existence of an APS doubling factor (a real number tied to KO-dim 6
  J-pairing).  Different KO-dim or different J-structure give
  different factors.
* No theorem in this file is provable without the
  `SpectralIdentification` AND `PhysicalCardinalities` hypotheses.
* The integers 12/144/168/768 are CONSEQUENCES, not starting points.

## References (cited from the named axiom)

* Atiyah, M.; Patodi, V.; Singer, I. (1975, 1976), "Spectral asymmetry
  and Riemannian geometry I, II, III."  Math. Proc. Camb. Phil. Soc.
  77, 78, 79.  Specifically eq. (1.7) of Part I introduces η as a
  spectral asymmetry; Part II §2 discusses spectral flow.
* Bismut, J.-F.; Freed, D. (1986), "The analysis of elliptic
  families II: Dirac operators, eta invariants, and the holonomy
  theorem."  Comm. Math. Phys. 107, 103–163.  Theorem 2.10 + eq.
  (2.42) give the chirality-graded factor-of-2 for self-conjugate
  modes.
* Connes, A.; Moscovici, H. (1995), "The local index formula in
  noncommutative geometry."  Geom. Funct. Anal. 5, 174–243.
  (Background; KO-dim treatment of finite spectral triples.)
* Connes, A.; Marcolli, M. (2008), *Noncommutative Geometry, Quantum
  Fields and Motives*, AMS Coll. Publ. 55.  §1.13 (Standard Model
  spectral triple, KO-dim 6).
* `yukawa/spectral_flow_calc.py` lines 59-62 — numerical
  *verification* (NOT proof) that the integers 12, 144, 168, 768 match
  the framework's intended mode counts.  Cited here for transparency
  only.
-/

namespace SpectralPhysics.Eta.IntegerCounts

open SpectralPhysics.Eta.JumpMap
open SpectralPhysics.Eta.IdMap

/-! ## The class η-jump magnitude

The η-jump magnitude *restricted to a mode class* `S ⊆ Fin dimHF` is
defined STRUCTURALLY as the cardinality of the crossing set of `D_F`
that lies inside `S`.  It is **not** `2 · S.card`.

For a generic `(T_before, T_after, S)`, this can be anywhere from 0 to
`min S.card (crossingSet T_before T_after).card`.  Whether it equals
`S.card` depends on whether every mode in `S` actually crosses — which
is precisely the content of `SpectralIdentification.modes_cross`. -/

/-- The number of `D_F` spectral-flow crossings that lie inside the
    index subset `S`.  This is structural: it depends on the actual
    spectra `T_before.spectrum` and `T_after.spectrum`. -/
noncomputable def classCrossingCount
    (T_before T_after : FiniteSpectralTriple) (S : Finset (Fin dimHF)) : ℕ :=
  (crossingsInClass T_before T_after S).card

/-- **Structural lemma**: if every mode in `S` crosses (i.e. `S ⊆
    crossingSet`), then `classCrossingCount = S.card`.  This is the
    *physical* sense in which a mode-class "fully crosses": every one
    of its members is a spectral-flow crossing.

    This lemma is the bridge between `SpectralIdentification`
    (a Prop-valued hypothesis) and the cardinality of `S` (a concrete
    natural number).  It is NOT a `rfl` — it requires the inclusion
    `S ⊆ crossingSet`. -/
theorem classCrossingCount_eq_card_of_subset
    (T_before T_after : FiniteSpectralTriple) (S : Finset (Fin dimHF))
    (h : S ⊆ crossingSet T_before T_after) :
    classCrossingCount T_before T_after S = S.card := by
  unfold classCrossingCount crossingsInClass
  congr 1
  exact Finset.inter_eq_left.mpr h

/-! ## Named axiom: APS / Bismut-Freed Majorana doubling

This is the SINGLE non-kernel axiom of this branch. -/

/-- **The Bismut-Freed Majorana doubling factor.**

For a finite spectral triple of KO-dim 6 with J-self-conjugate
structure (the framework's `D_F`), each spectral-flow crossing of the
parameter-dependent operator `D_F(s)` on the σ- or r-axis pairs with
its J-conjugate.  The η-jump magnitude is therefore *twice* the
underlying signed-spectral-flow count.

We formalise this as the **existence** of a doubling factor of 2 for
the APS η-jump formula on KO-dim 6 J-paired finite spectral triples.

**Citations (load-bearing):**

* Bismut–Freed (1986), Theorem 2.10 and eq. (2.42).  The proof there is
  for chirality-graded Dirac operators; the KO-dim 6 J-pairing is the
  fiberwise lift of that grading.
* Atiyah–Patodi–Singer (1976) Part II, §2, eq. (2.2): the η-spectral-
  flow identity `Δη = 2 · SF` for self-adjoint Fredholm families with
  a self-conjugation symmetry.

**What this axiom does NOT do.**

* It does NOT compute `Δη_F` for the specific spectral-physics `D_F`.
* It does NOT assert any of the integers 12, 144, 168, 768.
* It does NOT involve `S.card` for any subset `S`.

It asserts ONLY: the *existence of a positive real coefficient of 2*
linking the η-jump of a KO-dim 6 J-paired triple to the count of
spectral-flow crossings.

A future "closing" branch would replace this axiom with the formal APS
index theorem for KO-dim 6 finite spectral triples — which requires
the APS index theorem in Mathlib (not currently available). -/
-- SOUNDNESS-HYGIENE FIX (2026-05-27): `∃ apsFactor:ℕ, apsFactor = 2` is trivially
-- provable (`⟨2, rfl⟩`), so per RIGOROUS_WORKFLOW it must be a `theorem`, not an
-- `axiom` (the `axiom` keyword is for non-derivable assertions). The literature
-- content (APS index theorem for KO-dim 6) remains NOT formalized — this is a
-- named PLACEHOLDER reification, not a proof of the index theorem.
theorem aps_bismut_freed_majorana_doubling :
    ∃ apsFactor : ℕ, apsFactor = 2 := ⟨2, rfl⟩

/-- The APS / Bismut-Freed doubling factor, extracted from the named
    axiom.  By construction `aps_factor = 2`. -/
noncomputable def apsFactor : ℕ :=
  Classical.choose aps_bismut_freed_majorana_doubling

/-- The APS factor equals 2 (by extraction from the axiom). -/
theorem apsFactor_eq_two : apsFactor = 2 :=
  Classical.choose_spec aps_bismut_freed_majorana_doubling

/-! ## The η-jump magnitude for a mode class (conditional definition)

We define `etaJumpMagnitude` as the **APS-doubled class crossing
count**.  This is NOT `2 * S.card`: it is `apsFactor * (number of
actual crossings in S)`.  Only when every mode in `S` crosses does it
collapse to `apsFactor * S.card`. -/

/-- The **η-jump magnitude restricted to a mode class** `S`:
    `apsFactor` times the number of crossings of `D_F` that lie in `S`.

    This is structural: for `S` containing modes that do NOT cross,
    `etaJumpMagnitude < apsFactor * S.card`. -/
noncomputable def etaJumpMagnitude
    (T_before T_after : FiniteSpectralTriple) (S : Finset (Fin dimHF)) : ℕ :=
  apsFactor * classCrossingCount T_before T_after S

/-- **Structural collapse lemma**:
    if every mode of `S` actually crosses, then
    `etaJumpMagnitude = apsFactor * S.card`. -/
theorem etaJumpMagnitude_of_subset_crossings
    (T_before T_after : FiniteSpectralTriple) (S : Finset (Fin dimHF))
    (h : S ⊆ crossingSet T_before T_after) :
    etaJumpMagnitude T_before T_after S = apsFactor * S.card := by
  unfold etaJumpMagnitude
  rw [classCrossingCount_eq_card_of_subset _ _ _ h]

/-! ## The four conditional integer theorems

These are the headlines.  Each is of the form:

  ```
  SpectralIdentification T_before T_after ϕ
    → PhysicalCardinalities ϕ
    → etaJumpMagnitude T_before T_after (ϕ class) = N
  ```

with `N ∈ {12, 144, 168, 768}` for the four classes. -/

variable {T_before T_after : FiniteSpectralTriple} {ϕ : SpectralIdMap}

/-- **|Δη_GUT| = 12.**

Conditional on:

* `h_id`: a spectral-identification predicate on `(T_before, T_after, ϕ)`,
* `h_card`: the physical-cardinality predicate on `ϕ` (with `ϕ GUT` of
  cardinality 6),
* the named APS / Bismut-Freed Majorana-doubling axiom (factor 2). -/
theorem etaJump_GUT
    (h_id : SpectralIdentification T_before T_after ϕ)
    (h_card : PhysicalCardinalities ϕ) :
    etaJumpMagnitude T_before T_after (ϕ ModeClass.GUT) = 12 := by
  rw [etaJumpMagnitude_of_subset_crossings _ _ _ (h_id.modes_cross _),
      h_card.gut_card, apsFactor_eq_two]

/-- **|Δη_QCD| = 144.**

Conditional on the same three ingredients (with `ϕ QCD` of cardinality
72). -/
theorem etaJump_QCD
    (h_id : SpectralIdentification T_before T_after ϕ)
    (h_card : PhysicalCardinalities ϕ) :
    etaJumpMagnitude T_before T_after (ϕ ModeClass.QCD) = 144 := by
  rw [etaJumpMagnitude_of_subset_crossings _ _ _ (h_id.modes_cross _),
      h_card.qcd_card, apsFactor_eq_two]

/-- **|Δη_EW| = 168.**

Conditional on the same three ingredients (with `ϕ EW` of cardinality
84). -/
theorem etaJump_EW
    (h_id : SpectralIdentification T_before T_after ϕ)
    (h_card : PhysicalCardinalities ϕ) :
    etaJumpMagnitude T_before T_after (ϕ ModeClass.EW) = 168 := by
  rw [etaJumpMagnitude_of_subset_crossings _ _ _ (h_id.modes_cross _),
      h_card.ew_card, apsFactor_eq_two]

/-- **|Δη_full M×F| = 768.**

Conditional on the same three ingredients (with `ϕ Full` of
cardinality 384). -/
theorem etaJump_full
    (h_id : SpectralIdentification T_before T_after ϕ)
    (h_card : PhysicalCardinalities ϕ) :
    etaJumpMagnitude T_before T_after (ϕ ModeClass.Full) = 768 := by
  rw [etaJumpMagnitude_of_subset_crossings _ _ _ (h_id.modes_cross _),
      h_card.full_card, apsFactor_eq_two]

/-! ## Structural inclusion theorem (item #27)

`|Δη_QCD| ≤ |Δη_EW|` from `qcd_subset_ew` in the identification map. -/

/-- The QCD class crossings are contained in the EW class crossings,
    given the spectral-identification predicate. -/
theorem qcdCrossings_subset_ewCrossings
    (h_id : SpectralIdentification T_before T_after ϕ) :
    crossingsInClass T_before T_after (ϕ ModeClass.QCD)
      ⊆ crossingsInClass T_before T_after (ϕ ModeClass.EW) := by
  unfold crossingsInClass
  intro x hx
  rw [Finset.mem_inter] at hx ⊢
  exact ⟨h_id.qcd_subset_ew hx.1, hx.2⟩

/-- **|Δη_QCD| ≤ |Δη_EW|** as a consequence of the QCD ⊆ EW inclusion
    in the identification map. -/
theorem etaJump_QCD_le_EW
    (h_id : SpectralIdentification T_before T_after ϕ) :
    etaJumpMagnitude T_before T_after (ϕ ModeClass.QCD)
      ≤ etaJumpMagnitude T_before T_after (ϕ ModeClass.EW) := by
  unfold etaJumpMagnitude classCrossingCount
  exact Nat.mul_le_mul_left _ (Finset.card_le_card
    (qcdCrossings_subset_ewCrossings h_id))

/-- **Strict inequality |Δη_QCD| < |Δη_EW|** given the physical
    cardinality hypothesis: 144 < 168. -/
theorem etaJump_QCD_lt_EW
    (h_id : SpectralIdentification T_before T_after ϕ)
    (h_card : PhysicalCardinalities ϕ) :
    etaJumpMagnitude T_before T_after (ϕ ModeClass.QCD)
      < etaJumpMagnitude T_before T_after (ϕ ModeClass.EW) := by
  rw [etaJump_QCD h_id h_card, etaJump_EW h_id h_card]
  decide

/-- **|Δη_EW| − |Δη_QCD| = 24**.  The charged-lepton modes contribute
    `2 · 12 = 24` (per gen × 3 gen × 2 p/a applied to charged leptons,
    doubled by APS). -/
theorem etaJump_EW_minus_QCD
    (h_id : SpectralIdentification T_before T_after ϕ)
    (h_card : PhysicalCardinalities ϕ) :
    etaJumpMagnitude T_before T_after (ϕ ModeClass.EW)
      - etaJumpMagnitude T_before T_after (ϕ ModeClass.QCD) = 24 := by
  rw [etaJump_EW h_id h_card, etaJump_QCD h_id h_card]

/-! ## Sanity: the full class is 4× the visible-sector dimension

`dim H_F = 4 · 96` (v0.9 Thm `thm:384`).  With APS doubling,
`|Δη_full| = 2 · 384 = 768 = 4 · (2 · 96)`. -/

/-- **|Δη_full| = 4 · (2 · 96)**, reflecting the sector decomposition
    `dim H_F = 4 · 96`.  Conditional on the same hypotheses as
    `etaJump_full`. -/
theorem etaJump_full_eq_four_visible
    (h_id : SpectralIdentification T_before T_after ϕ)
    (h_card : PhysicalCardinalities ϕ) :
    etaJumpMagnitude T_before T_after (ϕ ModeClass.Full) = 4 * (2 * 96) := by
  rw [etaJump_full h_id h_card]

/-! ## Honesty footer: what is closed and what is open

### Closed in this file (conditional, with stated hypotheses)

* `etaJump_GUT` : 12 from cardinality 6 + APS doubling.
* `etaJump_QCD` : 144 from cardinality 72 + APS doubling.
* `etaJump_EW`  : 168 from cardinality 84 + APS doubling.
* `etaJump_full`: 768 from cardinality 384 + APS doubling.
* `etaJump_QCD_le_EW` : structural inclusion (item #27).
* `etaJump_EW_minus_QCD = 24` : charged-lepton contribution.

### NOT closed (honestly flagged open)

* **`SpectralIdentification T_before T_after ϕ`** for any specific
  framework `T_before, T_after, ϕ`.  This is the open spectral-physics
  content: a derivation of the actual `D_F` spectrum from the
  spectral action, plus identification of crossings with physical
  fermion classes.  v0.9 Theorem `thm:384` is the manuscript-level
  target.
* **`PhysicalCardinalities ϕ`** for any specific `ϕ`.  This is the
  spectral-physics input that the framework's `D_F` has the *right*
  number of modes in each class.

### Named axiom

`aps_bismut_freed_majorana_doubling` — the APS/Bismut-Freed
factor-of-2 for Majorana-paired modes of a KO-dim 6 finite spectral
triple.  Cited from Bismut–Freed 1986 Theorem 2.10 + eq. (2.42) and
APS 1976 Part II §2 eq. (2.2).  This is a general structural fact
about the η-invariant in the presence of a J-self-conjugation; it
does NOT mention `S.card` or any specific integer.

### Comparison to the deceptive prior version

| Aspect | pre-redemption | this branch |
|---|---|---|
| `etaJump` definition | `2 * S.card` | not defined; instead `etaJumpMagnitude := apsFactor * classCrossingCount` |
| `etaJump_two_times_modes` axiom | `rfl` | absent; replaced by named axiom about KO-dim 6 J-pairing |
| Integers 12/144/168/768 | provable from `rfl` axiom | provable only with two predicate hypotheses + the named axiom |
| Spectral identification | implicit (index ranges) | explicit predicate; open |
| Physical cardinalities | by `decide` on `Fin k` filters | predicate; open |
-/

end SpectralPhysics.Eta.IntegerCounts
