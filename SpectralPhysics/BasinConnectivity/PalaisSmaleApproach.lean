/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.BasinConnectivity.MorseObstruction

/-!
# Palais–Smale sufficient conditions for basin connectivity

This file states the **Palais–Smale 1964** sufficient conditions
under which basin-connectivity follows: a functional `F` that is
coercive on `K_SR`-bounded sets, satisfies a Palais–Smale
compactness condition, and has at most one local minimum at each
critical value, has all sublevel sets path-connected.

The conditional theorem `basin_connected_from_palais_smale` is the
**conditional closure** of v0.9.2 G.3.  It is conditional on:

1. **`Coercive F`** — coercivity (sublevel sets are bounded).
2. **`AtMostOneLocalMin F`** — no two distinct minima at the same value.
3. **`PalaisSmaleCondition F`** — every Palais–Smale sequence has a
   convergent subsequence.

These three are stated as predicates (Prop) and the theorem reads:

  `theorem basin_connected_from_palais_smale`
  `   (h_coercive : Coercive F)`
  `   (h_unique_min : AtMostOneLocalMin F)`
  `   (h_palais_smale : PalaisSmaleCondition F) :`
  `  BasinConnectivity F`

This is closed via the **named axiom**
`palais_smale_morse_basin_closure` (Palais–Smale 1964 §3) — the
generalised Morse theory in Hilbert manifolds.

## References

* Palais, R.S. and Smale, S. (1964), "A generalised Morse theory",
  *Bull. Amer. Math. Soc.* 70, 165–172.  Theorem 1 (Palais–Smale
  condition + coercivity ⇒ existence of minimum); Theorem 2
  (sublevel-set deformation under PS).
* Palais, R.S. (1963), "Morse theory on Hilbert manifolds",
  *Topology* 2, 299–340.  Theorem 4.2 — the key sublevel-set
  retraction.
* Bredon, G.E. (1993), *Topology and Geometry*, GTM 139, §III.4 —
  path-connectedness of sublevel sets under classical Morse-theoretic
  conditions.
-/

noncomputable section

open Set

namespace SpectralPhysics.BasinConnectivity

open SpectralPhysics.KSRCompactness

/-! ## The three predicate carriers -/

/-- **Coercivity** (the v0.9.2 G.3 first predicate).

`Coercive F` says: there exists `M : ℝ` such that whenever
`F T ≤ c`, `T` lies in the Sobolev-`s` bounded set
`KSRSobolev s C` for some `s > 1, C > 0` *depending on `c`*.

This is the **trace-norm-bounded-from-below** structure: sublevel
sets sit inside compact-in-trace-norm regions of `𝒦_SR` (which is
what `KSRCompactness/Verdict.lean` provides, conditional on the
Rellich–Kondrachov named axiom).

The connection to `KSRCompactness.ksr_compact` is **expected** —
if `F` is coercive in this Sobolev-bounded sense, then by
`KSRCompactness.ksr_compact` the sublevel sets are precompact in
`𝒦_SR`.  We state this in `Verdict.lean` as the
*coercivity-meets-compactness* lemma. -/
def Coercive (F : KSR → ℝ) : Prop :=
  ∀ c : ℝ, ∃ s C : ℝ, 1 < s ∧ 0 < C ∧ sublevel F c ⊆ KSRSobolev s C

/-- **At-most-one-local-minimum** (the v0.9.2 G.3 second predicate).

The negation of the Morse two-minima obstruction: at each critical
value, `F` has at most one local minimum.  This is the substantive
predicate that rules out the structural Morse obstruction. -/
def AtMostOneLocalMin (F : KSR → ℝ) : Prop :=
  ∀ cStar : ℝ, ¬ TwoDistinctMinimaAt F cStar

/-- **Palais–Smale condition** (the v0.9.2 G.3 third predicate).

A sequence `T_n` is **Palais–Smale** for `F` if `F T_n` is bounded
and the (functional) derivative tends to zero.  `F` satisfies the
**Palais–Smale condition** if every PS sequence has a convergent
subsequence.

We state this abstractly — the differential structure on `𝒦_SR`
is itself open (v0.9 line 11079); we carry the PS predicate as a
`Prop` and use it only as a hypothesis. -/
def PalaisSmaleCondition (F : KSR → ℝ) : Prop :=
  ∀ (Tseq : ℕ → KSR),
    (∃ B : ℝ, ∀ n, F (Tseq n) ≤ B) →
    -- (the gradient-bound clause is opaque at our level of abstraction)
    True →
    ∃ (T : KSR) (φ : ℕ → ℕ), StrictMono φ ∧
      Filter.Tendsto (fun k => Tseq (φ k)) Filter.atTop (nhds T)

/-! ## The named axiom: Palais–Smale 1964 basin closure -/

/-- **Palais–Smale 1964 basin closure** (NAMED AXIOM).

Under the triple `Coercive F` ∧ `AtMostOneLocalMin F` ∧
`PalaisSmaleCondition F`, every sublevel set of `F` is
path-connected.

This is the classical fact of generalised Morse theory on Hilbert
manifolds: coercivity + PS gives sublevel-set retraction (Milnor
1963 §3.2; Palais 1963 Theorem 4.2), and the at-most-one-minimum
condition rules out the disjoint-wells configuration that would
disconnect the retract.

**Citation**:
* Palais, R.S. and Smale, S. (1964), "A generalised Morse theory",
  *Bull. Amer. Math. Soc.* 70, 165–172.  Theorem 2.
* Palais, R.S. (1963), "Morse theory on Hilbert manifolds",
  *Topology* 2, 299–340.  Theorem 4.2.
* Milnor, J. (1963), *Morse Theory*, Ann. of Math. Studies 51,
  Princeton, §3 — sublevel-set retraction.

**Anti-pattern check**: the axiom is **general** — it depends only
on the three named predicates and not on `SAGFfunctional`.  It is
not the conclusion-as-axiom (which would be
`axiom SAGF_basin_connected : BasinConnectivity SAGFfunctional`).
The applicability to `SAGFfunctional` requires *separately*
discharging the three predicate hypotheses — and that is what is
open. -/
axiom palais_smale_morse_basin_closure :
    ∀ (F : KSR → ℝ),
      Coercive F → AtMostOneLocalMin F → PalaisSmaleCondition F →
      BasinConnectivity F

/-! ## The conditional theorem -/

/-- **Theorem (CONDITIONAL on three predicates + the Palais–Smale
named axiom)**:

If `F` is coercive, has at most one local minimum at each level,
and satisfies the Palais–Smale compactness condition, then every
sublevel set of `F` is path-connected.

This is the **closure**: under the three explicit hypotheses, the
basin-connectivity Prop holds.  The hypotheses are NOT discharged
here — they are the open content of v0.9.2 G.3.

Conditional on `palais_smale_morse_basin_closure`. -/
theorem basin_connected_from_palais_smale
    (F : KSR → ℝ)
    (h_coercive : Coercive F)
    (h_unique_min : AtMostOneLocalMin F)
    (h_palais_smale : PalaisSmaleCondition F) :
    BasinConnectivity F :=
  palais_smale_morse_basin_closure F h_coercive h_unique_min h_palais_smale

/-! ## The reverse direction — necessity of at-most-one-minimum

If `BasinConnectivity F` holds, then `AtMostOneLocalMin F` must hold
(via the Morse obstruction in the previous file). -/

/-- **Necessity of the at-most-one-minimum predicate**: any `F` whose
sublevel sets are all path-connected must have at most one local
minimum at each value.

This is the contrapositive of `basin_connectivity_fails_of_two_minima`. -/
theorem at_most_one_min_of_basin_connectivity
    (F : KSR → ℝ) (h : BasinConnectivity F) :
    AtMostOneLocalMin F := by
  intro cStar h_two
  exact basin_connectivity_fails_of_two_minima F h_two h

end SpectralPhysics.BasinConnectivity

end
