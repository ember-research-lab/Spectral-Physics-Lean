/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.RMForcesDivisionAlgebras.ReadingA_FormalChain
import SpectralPhysics.RMForcesDivisionAlgebras.ReadingB_TraceState
import SpectralPhysics.RMForcesDivisionAlgebras.ReadingC_NaturalityForcesAlt
import SpectralPhysics.RMForcesDivisionAlgebras.CounterexampleClass

/-!
# Combined Verdict — Does `R ∘ M = id` Force the Hurwitz Tower?

## The v0.9.2 deferred item G.4

v0.9 line 16779 self-flags as **"Real gap"** the claim that
Axiom 3 (Reconstruction `R ∘ M = id` + Naturality) forces the
observation algebra to be a normed division algebra — i.e. one of
`{ℝ, ℂ, ℍ, 𝕆}` (Hurwitz 1898).

This dispatch breaks the chain into four links, finds that one of
them is load-bearing-and-open, and constructs an **explicit
counterexample** that satisfies the starting predicates but fails
the target.

## Per-reading summary

| Reading | Question | Verdict |
|---------|----------|---------|
| A (formal chain) | Four-link structural decomposition | **Tier-3 chain** |
| B (trace state) | Faithful trace ⇒ composition norm? | **NO** (open) |
| C (naturality)  | Naturality ⇒ alternativity?       | **NO** (open) |
| Counterex.      | `ℝ × ℝ` satisfies starting predicates, not target | **YES**, explicit |

## Combined verdict

**`R ∘ M = id` (Axiom 3 (i)) and Naturality (Axiom 3 (ii)) do NOT
force the Hurwitz tower.**

The counterexample `Counterexample := ℝ × ℝ` satisfies:
* Link 1 (faithful trace)
* Link 3 (alternativity, via associativity)
* `finrank ℝ = 2` (compatible with the Hurwitz dimension set)

but fails:
* the *strong* Link 2 (no faithful composition norm exists, because
  zero divisors `(1, 0) · (0, 1) = (0, 0)`)
* isomorphism with `ℂ` (the Hurwitz-tower entry at dimension `2`).

The honest framing: Axiom 3 needs an **additional structural
hypothesis** to close the chain.  Candidates the v0.9 manuscript
could supply (and which would close the gap if added explicitly):

* a *positivity* axiom forcing all observables to have non-negative
  spectrum *and* the trace to be a faithful state in the strong
  GNS sense (Connes 1994, Ch. V);
* a *unitarity-from-reconstruction* argument forcing the propagator
  to preserve a Hilbert-space norm satisfying the composition law;
* a direct postulate that the algebra is a Banach algebra with
  `‖ab‖ = ‖a‖ · ‖b‖` (essentially circular — postulating Link 2).

## Consequences

* **OP3 standing**: G.4 closure is **NOT** available from Axiom 3
  alone; v0.9 line 16779's "Real gap" self-flag is **vindicated**
  by the explicit counterexample.
* **Hurwitz forcing**: remains a **conditional** result — conditional
  on the composition-norm hypothesis being supplied externally.
  (`SpectralPhysics/Algebra/Forcing.lean` already takes
  `CompositionAlgebra A` as a typeclass *hypothesis*; this dispatch
  formalizes the obstruction to deriving that hypothesis from
  Axiom 3.)
* **v1.0 framing**: the framework's claim "division algebras arise
  from self-referential closure" requires either (a) a stronger
  Axiom 3, or (b) a transcendent-IC framing of the algebra type.

## Named axioms cited

* **Hurwitz, A. (1898/1923).** "Über die Composition der quadratischen
  Formen." — cited via `composition_dim_le_eight_axiom` in `Hurwitz.lean`.
* **Albert, A.A. (1947).** "Absolute valued real algebras."  Ann. Math. 48.
  — identifies `ℝ × ℝ` as the canonical non-division 2-dim ℝ-algebra.
* **Bruck, R.H. & Kleinfeld, E. (1951).** "The structure of alternative
  division rings."  Proc. AMS 2. — composition ↔ alternative for real algebras.
* **Connes, A. (1994).** *Noncommutative Geometry*, Ch. V. — GNS faithful
  state construction; required positivity for Link 1 → Link 2.

This dispatch introduces **zero new axioms**.

## Cross-references

* `compute/faithfulness-forces-yR` — adjacent negative on `y_R`
  closure from Axiom 3 (five readings A/B/C/D/E all NO).
* `SpectralPhysics/Algebra/Hurwitz.lean` — Hurwitz tower (Tier-1
  conditional on `CompositionAlgebra`).
* `SpectralPhysics/Algebra/Forcing.lean` — division-algebra
  forcing assuming the composition-algebra structure.
-/

namespace SpectralPhysics.RMForcesDivisionAlgebras

/-! ## The headline verdict -/

/-- **Headline theorem — Axiom 3 alone does NOT force the Hurwitz
tower.**

There exists a finite-dimensional ℝ-algebra `A` (namely `ℝ × ℝ`)
that satisfies the starting predicates of the formal chain
(faithful trace, alternativity, `finrank = 2`) but is **not**
isomorphic to any Hurwitz-tower entry — in particular, not to `ℂ`.

This is the v0.9.2 honest negative result for deferred item G.4. -/
theorem RM_does_not_force_division_algebras_headline :
    ∃ A : Type,
      ∃ _ : CommRing A, ∃ _ : Algebra ℝ A,
      ∃ _ : Star A,
        Link1_FaithfulTrace A ∧
        Link3_Alternative A ∧
        Module.finrank ℝ A = 2 ∧
        ¬ StrongLink2_FaithfulCompositionNorm A ∧
        IsEmpty (A ≃+* ℂ) := by
  refine ⟨Counterexample, inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨counterexample_link1,
         counterexample_link3,
         counterexample_finrank,
         counterexample_fails_strong_link2,
         counterexample_not_iso_complex⟩

/-- **Compact restatement** — for the headline-grade summary:

There exists a Type (the explicit `ℝ × ℝ`) that violates the v0.9
"R ∘ M = id forces Hurwitz" claim while satisfying its premises. -/
theorem v092_G4_verdict_NO :
    ¬ ∀ (A : Type) [Ring A] [Algebra ℝ A] [Star A]
        [FiniteDimensional ℝ A],
        Link1_FaithfulTrace A → Link3_Alternative A →
        StrongLink2_FaithfulCompositionNorm A := by
  intro h
  -- Apply h to A = Counterexample with the satisfied premises
  have h_strong := h Counterexample
    counterexample_link1 counterexample_link3
  exact counterexample_fails_strong_link2 h_strong

/-! ## The honest accounting

* Link 1 (faithful trace): **Tier-3** content from Axiom 3 (i).
  Travels as `Link1_FaithfulTrace`.  Satisfied by the counterexample.
* Link 2 (composition norm): **Tier-3** load-bearing step.  Travels
  as `Link2_CompositionNorm` (weak) and
  `StrongLink2_FaithfulCompositionNorm` (strong).  The weak version
  is trivially satisfiable; the strong version is **falsified** by
  the counterexample.
* Link 3 (alternativity): **Tier-3** content from Axiom 3 (ii).
  Travels as `Link3_Alternative`.  Satisfied by the counterexample.
* Link 4 (Hurwitz tower): **Tier-1** via the existing
  `composition_dim_le_eight_axiom` in `Hurwitz.lean` (Hurwitz 1898). -/

/-- **Why-this-matters summary** — the counterexample identifies the
exact missing ingredient (faithful composition norm) and shows that
the v0.9 claim cannot be discharged without an additional axiom or
structural hypothesis. -/
theorem missing_ingredient_is_strong_link_2 :
    StrongLink2_FaithfulCompositionNorm Counterexample → False :=
  counterexample_fails_strong_link2

end SpectralPhysics.RMForcesDivisionAlgebras
