# CompositionBroaderUniqueness — Honest STATUS (v0.9.2 / A.1)

**Branch**: `compute/composition-broader-uniqueness`
**Target**: v0.9.2 deferred item A.1 — composition uniqueness
against non-Kasparov factorizations
(`yukawa/pre_geometric/v091_v092_split_audit/v092_deferred.md`,
§A.1).
**Path**: v1.0 NCG-extension target; v0.9.1 closed the
Kasparov-product scope (Path A), this branch closes the named
non-Kasparov candidates.
**Audit precedent**: this branch follows the discipline
established in `compute/self-model-deficit-rigorous` and reused
in v0.9.1's `compute/composition-uniqueness` (Path A).
**Session connection**:
`pre_geometric/Kunneth_composition_theorem/verdict.md` (PARTIAL /
NEED-EXTENSION) — K1+K2+K3 close the Kasparov scope but not the
free-probability scope; this branch is the Lean witness for the
named-candidate fragment of the v0.9.2 split.

---

## 1. Files

| File | Role |
|------|------|
| `NonKasparovCandidates.lean` | Defines four non-Kasparov shadows (free-Voiculescu `⊞`, multiplicative-free `⊠`, monoidal-non-Kasparov, boxed `⊞ₐ`) as `BinaryOpOnSpectra`; records each one's literature provenance as a Prop-bearing `Shadow` structure. |
| `TraceLevelDistinction.lean` | Tier-1 falsifiers: each non-Kasparov candidate (incl. boxed at `a=1`) violates Hamiltonian additivity on an explicit witness pair, hence fails the v0.9.1 three-condition predicate. Re-uses `three_conditions_force_trace_law` via the contrapositive lemma `trace_mismatch_excludes_three_conditions`. |
| `HigherMomentObstruction.lean` | Headline Tier-1 conditional closure: `broader_uniqueness_among_named_candidates` — every named candidate satisfying ThreeConditions equals `additive`. |
| `UncountableObstruction.lean` | Honest open content: `BroaderUniquenessAllNonKasparov` predicate (over all `BinaryOpOnSpectra`), and its equivalence with the named free-probability research program `FreeProbResearchProgram`. |
| `Verdict.lean` | Module-level verdict (CONDITIONAL / PARTIAL); re-exports headline + open. Wired into `SpectralPhysics.lean`. |
| `STATUS.md` | This file. |

---

## 2. Tier-1 theorems (proved in Lean, zero new axioms)

All five `.lean` modules build cleanly under
`lake build SpectralPhysics` (3268 jobs as of this branch).  Zero
`sorry`, zero `admit`, zero `True` placeholders.

### Trace-level falsifiers (zero new axioms)

* `freeVoiculescu_violates_hamiltonian_additivity`
  Witness `μ₁ = {1,1}, ν₀ = {3}`: `trace(freeVoiculescuConv μ₁ ν₀) = 5`
  ≠ `|ν₀|·trace μ₁ + |μ₁|·trace ν₀ = 1·2 + 2·3 = 8`.

* `multFree_violates_hamiltonian_additivity`
  Witness `μ₀ = {2}, ν₀ = {3}`: `trace = 6 ≠ 5`.

* `monoidalNonK_violates_hamiltonian_additivity`
  Witness `μ₀ = {2}, ν₀ = {3}`: monoidal shadow shifts the additive
  multiset by `+1` per eigenvalue; trace = 6 ≠ 5.

* `boxed_violates_hamiltonian_additivity`
  Witness `μ₀ = {2}, ν₀ = {3}` at `a = 1`: boxed shadow damps the
  second-factor eigenvalue to zero; trace = 2 ≠ 5.

### Headline conditional closure (zero new axioms)

* `broader_uniqueness_among_named_candidates :`
  `  IsNamedCandidate op → ThreeConditions op → op = additive`
  Closure against the five-element named-candidate set
  `{additive, freeVoiculescuConv, multFreeConv, monoidalNonKConv, boxedConv 1}`.

* `named_candidate_pointwise_additive` — corollary: a named
  three-condition operation equals `additiveConv` pointwise.

* `named_candidate_trace_law` — corollary: trace-channel equality
  for any named three-condition operation (follows from v0.9.1
  Scope-2 unconditionally).

### Open-content predicates (NOT theorems, NOT axioms)

* `IsKasparov op := Nonempty (KasparovProductWitness op)` — uses
  the v0.9.1 structure; **NOT** `:= True`.

* `BroaderUniquenessAllNonKasparov : Prop` — the uncountable
  closure predicate.

* `FreeProbResearchProgram : Prop` — the literature-named alias,
  `def`-equal to the above.

* `v092_A1_open : BroaderUniquenessAllNonKasparov ↔ FreeProbResearchProgram`
  — `Iff.rfl`; the content is the **name**, fingering the exact
  open research program.

### Re-use lemma

* `trace_mismatch_excludes_three_conditions` — generic
  contrapositive of v0.9.1's `three_conditions_force_trace_law`.
  Used in each per-candidate falsifier.

---

## 3. Named axioms with citations

**Number of new axioms introduced by this branch: 0.**

Every Tier-1 theorem in this branch depends only on:

* `propext`
* `Classical.choice`
* `Quot.sound`

(the three Lean-kernel axioms).  See §6 for the full
`#print axioms` output.

The literature underlying the four named candidates is cited
**in the file docstrings** (not as Lean axioms):

| Citation | Provenance for |
|---|---|
| Voiculescu, D. (1985) "Symmetries of some reduced free product C*-algebras", LNM 1132 | `freeVoiculescuConv` shadow (the block-diagonal model is Nica–Speicher 2006 Example 8.10) |
| Voiculescu, D. (1991) "Limit laws for random matrices and free products", *Invent. Math.* 104 | Same |
| Speicher, R. (1994) "Multiplicative functions on the lattice of non-crossing partitions and free convolution", *Math. Ann.* 298 | Free convolution combinatorics (the additive-at-cumulants / divergent-at-moments split) |
| Nica, A., Speicher, R. (2006) *Lectures on the Combinatorics of Free Probability*, LMS LNS 335 | The §10.5–§11 moment-problem analogue identified with `FreeProbResearchProgram` |
| Bercovici, H., Voiculescu, D. (1993) "Free convolution of measures with unbounded support", *Indiana Univ. Math. J.* 42 | `multFreeConv` shadow (multiplicative `⊠`) |
| Joyal, A., Street, R. (1991) "The geometry of tensor calculus, I", *Adv. Math.* 88 | `monoidalNonKConv` shadow (non-Kasparov tensor cat coherence twist) |
| Bożejko, M., Bryc, W. (2006) "On a class of free Lévy laws related to a regression problem", *J. Funct. Anal.* 236 | `boxedConv a` family |
| Bryc, W. (2007) — the `a`-deformed cumulant relation (eq. 2.4) | Trace-shadow form of the boxed convolution |
| Mesland, B., Rennie, A. (2014) *J. Funct. Anal.* 271 | `IsKasparov` underlying structure (re-used from v0.9.1) |

**Smuggling check.** No literature citation is converted to a
Lean `axiom` that asserts the conclusion of any in-branch theorem.
In particular:

* No axiom of the form `∀ op, ThreeConditions op → op = additive`
  appears.
* No axiom of the form `IsKasparov op := True` appears.
* No axiom claims the uncountable closure
  `BroaderUniquenessAllNonKasparov`.

The closure of the named candidates is achieved by **direct
spectrum-level computation** on the explicit witness pairs.

---

## 4. Predicates carrying open content

| Predicate | File | Open content |
|---|---|---|
| `BroaderUniquenessAllNonKasparov` | `UncountableObstruction.lean` | Uncountable closure: every three-condition op is Kasparov-or-additive. Open in the free-probability literature. |
| `FreeProbResearchProgram` | `UncountableObstruction.lean` | `def`-alias for the above under its standard literature name. The "content" is the name. |

The two predicates are `def`-equivalent.  This is **intentional**:
solving v0.9.2 A.1 = solving the named free-probability research
program; no daylight between them.

---

## 5. Sorries

**Zero sorries.**  Verified by

```
$ grep -rn 'sorry\|admit' SpectralPhysics/CompositionBroaderUniqueness/
(no output)
```

---

## 6. `#print axioms` audit

```
'broader_uniqueness_among_named_candidates' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'verdict_named_closure' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'verdict_trace_channel' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'verdict_uncountable_open' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'freeVoiculescu_violates_hamiltonian_additivity' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'multFree_violates_hamiltonian_additivity' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'monoidalNonK_violates_hamiltonian_additivity' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'boxed_violates_hamiltonian_additivity' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'v092_A1_open' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'trace_channel_independent_of_uncountable_obstruction' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

**Every theorem carries zero non-kernel axioms.**  The
named-candidate closure goes through without re-axiomatising any
of v0.9.1's K1/K2/K3 axioms, and without introducing any new
free-probability axioms.  The literature is cited in docstrings;
the proofs reduce to direct multiset computation.

---

## 7. Build status

```
$ lake build SpectralPhysics
... (full build) ...
✔ [3267/3268] Built SpectralPhysics
Build completed successfully (3268 jobs).
```

---

## 8. Anti-pattern check (defensive)

The task brief explicitly forbids three anti-patterns.  This
branch confirms it complies with each:

* **No `IsKasparov op := True`.**  `IsKasparov` is defined as
  `Nonempty (KasparovProductWitness op)`, where
  `KasparovProductWitness` is the v0.9.1 structure carrying the
  symmetry + KK-product marker.  The disjunction in
  `BroaderUniquenessAllNonKasparov` is therefore non-vacuous.

* **No claim of uncountable closure without naming the missing
  free-probability axiom.**  The uncountable closure is recorded
  as the `BroaderUniquenessAllNonKasparov` predicate and
  identified with `FreeProbResearchProgram` (Nica–Speicher 2006
  §10.5–§11).  No axiom asserts it; the verdict is
  CONDITIONAL/PARTIAL.

* **No axiom-smuggling.**  The strongest form of in-branch
  axiom-smuggling — `axiom additive_unique_among_all : ∀ op …`
  — is absent.  In fact, this branch introduces **zero** new
  axioms; all closure is by direct multiset computation on
  explicit witness pairs.

---

## 9. Honest verdict

**Verdict: CONDITIONAL / PARTIAL.**

### Closed at Tier 1 (this branch, zero new axioms)

* Closure against the four **named** non-Kasparov candidates
  (free `⊞`, mult-free `⊠`, monoidal non-K, boxed `⊞ₐ` at `a=1`):
  Tier-1 closure via the explicit-witness trace-mismatch
  falsifiers, combined with v0.9.1's
  `three_conditions_force_trace_law`.

### Carried forward as honest open content

* **Uncountable closure** (every binary operation on `Spectrum`,
  not just the named four) is recorded as the
  `BroaderUniquenessAllNonKasparov` predicate.  Identified with
  the Nica–Speicher (2006) §10.5–§11 free-probability moment-problem
  research program (`FreeProbResearchProgram`).  Solving one
  solves the other; neither is closed in this branch.

* **Other interior `a ∈ (0,1)`** values of the boxed convolution.
  Tier-1 closure is given at `a = 1`; other values fail by the
  same trace mismatch but require per-`a` witnesses Lean does
  not iterate over.

### Exact scope statement

> Among `{additive, freeVoiculescuConv, multFreeConv,
> monoidalNonKConv, boxedConv 1}`, the v0.9.1 three-condition
> predicate selects exactly `additive` (proved Tier-1, zero new
> axioms).  Closure against **all** non-Kasparov factorizations is
> the open `BroaderUniquenessAllNonKasparov` predicate,
> definitionally equivalent to the named free-probability research
> program `FreeProbResearchProgram`.  This branch does **not**
> close the uncountable case; it identifies it.

### Connection to v0.9.1 verdicts

* v0.9.1's `CompositionUniqueness` was CONDITIONAL on K1+K2+K3
  for the Kasparov scope, plus OPEN for the broader pointwise
  claim.

* This branch (v0.9.2 A.1) populates the v0.9.1 "Scope 4 OPEN"
  predicate with named non-Kasparov candidates and closes the
  named subset.  The remaining uncountable content is now
  explicitly identified with a single named open conjecture
  (`FreeProbResearchProgram`), rather than carried as an
  unnamed predicate.

### Comparison to a hypothetical "closure-claiming" version

A future "fully closing" branch would need to either:

(a) Port Nica–Speicher (2006) §10.5–§11 into Mathlib at the
`Multiset ℝ` level, obtaining `BroaderUniquenessAllNonKasparov`
as a theorem.  This is the free-probability research program.

(b) Formalize unbounded KK-theory in Mathlib and show every
three-condition operation arises as a Kasparov product (giving
the `IsKasparov op` disjunct directly).  This is the operator-
algebraic NCG-extension program identified in
`v092_deferred.md` §A.

Neither (a) nor (b) is in this branch.  Neither is pretended.
