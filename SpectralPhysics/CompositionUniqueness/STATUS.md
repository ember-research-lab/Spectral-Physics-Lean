# CompositionUniqueness — Honest STATUS

**Branch**: `compute/composition-uniqueness` (this file)
**Target**: v0.9 line 16783 hand-wavy admission
**Path**: A (per `pre_geometric/v091_refactor/composition_decision.md`)
**Audit precedent**: this branch redeems the audit-caught prior
version (see §5 below) and follows the discipline established in
`compute/self-model-deficit-rigorous`.

This file is the **honest accounting** of what this branch
delivers and what it deliberately does not.

---

## 1. Theorems proved (with statements)

All eight `.lean` modules in this directory build cleanly under
`lake build SpectralPhysics` (3179 jobs, full repo).  Zero
`sorry`, zero `admit`, zero `True` placeholders.

The module operates at **four distinct scopes**, labelled
explicitly as CLOSED / CONDITIONAL / OPEN.

### Scope 1 (CLOSED, modulo two cited Minkowski-cancellation axioms)

* `additive_is_unique_among_three_named (c : NamedConvolution) :`
  `  ThreeConditions c.toOp ↔ c = NamedConvolution.additive`
  Among the three named candidates (additive, multiplicative,
  free), only additive satisfies the three-condition predicate.

### Scope 2 (CLOSED unconditionally — ZERO new axioms)

* `three_conditions_force_trace_law :`
  `  ∀ op (h : ThreeConditions op) μ ν,`
  `    Spectrum.trace (op μ ν) = Spectrum.trace (additiveConv μ ν)`
  Any binary operation satisfying the three conditions agrees
  with additive convolution on the trace functional.

* `three_conditions_trace_unique` — corollary: any two
  three-condition operations have the same trace functional on
  every spectrum pair.

* `trace_uniqueness_of_hamiltonian_additivity` (the underlying
  unconditional lemma in `BroaderUniquenessOpen.lean`).

### Scope 3 (CONDITIONAL on K1+K2+K3)

* `kasparov_product_satisfies_three_conditions :`
  `  ∀ {op} (h : KasparovProductWitness op), ThreeConditions op`
  Within the category of Kasparov-product spectral operations,
  the three-condition predicate is necessarily satisfied.  Uses
  the three named axioms K1+K2+K3 (citations in §2 below).

* `kasparov_product_trace_eq_additive` — corollary: the trace
  channel agrees with additive convolution.

* `kasparov_three_conditions` — re-export in `Theorem.lean`.

### Scope 4 (HONESTLY OPEN — predicate, not theorem, not axiom)

* `PointwiseUniqueness : Prop` (`BroaderUniquenessOpen.lean`)
  The v0.9 line 16783 claim, stated as a `Prop`.  Not proved.

* `BroaderUniqueness (op : BinaryOpOnSpectra) : Prop` — the
  implication form.  Not proved (in general).

* `additive_satisfies_broader_uniqueness` — trivially true for
  additive itself (`additiveConv μ ν = additiveConv μ ν`); has
  NO content.  Included only as a sanity check.

* `composition_uniqueness_under_broader_hypothesis` — the
  conditional form: assuming `PointwiseUniqueness` as a
  hypothesis, the v0.9 admission is closed.  The hypothesis IS
  the open problem; it is not discharged.

* `composition_unique_conditional_on_broader` — same in
  `Theorem.lean`.

### Auxiliary positive results (used internally)

* `additive_satisfies_three_conditions` — additive convolution
  satisfies the three conditions (uses Minkowski axioms).
* `multiplicative_violates_hamiltonian_additivity` — zero axioms.
* `multiplicative_not_three_conditions` — zero axioms.
* `free_violates_hamiltonian_additivity` — zero axioms.
* `free_not_three_conditions` — zero axioms.
* `additive_satisfies_hamiltonian` — zero axioms.
* `additive_satisfies_hurwitz` — zero axioms.
* `additive_satisfies_faithfulness` — uses Minkowski axioms.

---

## 2. Named axioms (5 total, all cited)

### K1 — `K1_mesland_rennie_card` (`KasparovProductUniqueness.lean`)

> `∀ {op}, KasparovProductWitness op → ∀ μ ν,`
> `  Multiset.card (op μ ν) = Multiset.card μ * Multiset.card ν`

Spectrum-side shadow of the cardinality (= dimension) channel of
the unbounded Kasparov product.

**Citation**: Mesland, B., "Unbounded bivariant K-theory and
correspondences in noncommutative geometry", arXiv:1304.3802,
*J. Reine Angew. Math.* 691 (2014); Mesland, B., Rennie, A.,
"Nonunital spectral triples and metric completeness in unbounded
KK-theory", arXiv:1502.04520, *J. Funct. Anal.* 271 (2016).

### K2 — `K2_rosenberg_schochet_cancel` (`KasparovProductUniqueness.lean`)

> `∀ {op}, KasparovProductWitness op → ∀ μ μ' ν, ν.NonTrivial →`
> `  op μ ν = op μ' ν → μ = μ'`

Spectrum-side shadow of the KK-Künneth short exact sequence
(left cancellation form).

**Citation**: Rosenberg, J., Schochet, C., "The Künneth theorem
and the universal coefficient theorem for Kasparov's generalized
K-functor", *Duke Math. J.* 55 (1987), 431–474.

### K3 — `K3_kassel_residue` (`KasparovProductUniqueness.lean`)

> `∀ {op}, KasparovProductWitness op → HamiltonianAdditivity op`

Spectrum-side shadow of the multiplicativity of the
noncommutative residue under exterior products of spectral
triples.

**Citation**: Kassel, C., "Cyclic homology, comodules, and mixed
complexes", *J. Algebra* 107 (1987), 195–216; Kassel, C., "Le
résidu non commutatif (d'après M. Wodzicki)", *Sém. Bourbaki*
708, *Astérisque* 177–178 (1989).

### `minkowski_left_cancel`, `minkowski_right_cancel` (`AdditiveSatisfies.lean`)

> `∀ μ μ' ν, ν.NonTrivial → additiveConv μ ν = additiveConv μ' ν → μ = μ'`
> (and the symmetric form)

Generic additive-combinatorics facts about Minkowski sums of
multisets of reals.  Standard, but not yet in Mathlib's
`Multiset` API.

**Citation**: Lev, V., Yuster, R., "Restricted set addition in
groups, I", *J. Algebra* 211 (1999); Nathanson, *Additive Number
Theory* (Springer GTM 165, 1996), Ch. 1; Tao, T., Vu, V.,
*Additive Combinatorics* (Cambridge SAM 105, 2006), §2.4.

### Smuggling check

Each named axiom is a **generic mathematical fact** citing a
specific paper that proves the underlying NCG / combinatorics
content.  None of them asserts the conclusion of this module's
theorem (the broader pointwise uniqueness).  In particular:

* K1+K2+K3 give the *forward* direction (any Kasparov product
  satisfies the three conditions); they do **not** give the
  *reverse* direction (any three-condition operation is a
  Kasparov product).  The reverse direction is exactly the
  broader uniqueness, which we record as OPEN.

* The Minkowski-cancellation axioms are about the additive
  convolution being well-behaved as a multiset operation; they
  say nothing about other binary operations and contribute
  nothing to ruling out non-additive operations.

* The audit-caught prior axiom
  `three_conditions_force_higher_moments` (which asserted the
  conclusion: any three-condition operation matches additive on
  all moments, hence on the spectrum) is **absent**.  The
  redemption is exactly this: that load-bearing claim is now
  Scope 4 (predicate, not theorem, not axiom).

---

## 3. Sorries — categorised

**Zero sorries.**  Verified by
`grep -rn 'sorry\|admit' SpectralPhysics/CompositionUniqueness/`.

The "openness" of this branch is encoded *not* via `sorry` but via
the explicit Scope-4 predicate `PointwiseUniqueness`.  The moral
equivalent of a `sorry` would be to declare it as an axiom; we
deliberately do **not**.

---

## 4. What is closed vs. open

### Genuinely closed (proved unconditionally — zero non-kernel axioms)

* `three_conditions_force_trace_law` (Scope 2 unconditional)
* `three_conditions_trace_unique` (corollary)
* `trace_uniqueness_of_hamiltonian_additivity`
* `multiplicative_violates_hamiltonian_additivity`
* `multiplicative_not_three_conditions`
* `free_violates_hamiltonian_additivity`
* `free_not_three_conditions`
* `additive_satisfies_hamiltonian`
* `additive_satisfies_hurwitz`

### Closed conditionally on the two Minkowski-cancellation axioms

* `additive_is_unique_among_three_named` (Scope 1)
* `additive_satisfies_three_conditions`
* `additive_satisfies_faithfulness`

### Closed conditionally on K1+K2+K3 (Path A — Kasparov-narrow)

* `kasparov_product_satisfies_three_conditions` (Scope 3)
* `kasparov_three_conditions`
* `kasparov_product_trace_eq_additive` (this one only needs K3)

### Honestly open

* `PointwiseUniqueness` itself (the original v0.9 line 16783
  claim).  Recorded as a predicate; Path A declares it a v1.0
  NCG-extension target.

---

## 5. Comparison to the audit-caught prior version

The prior `compute/composition-uniqueness` branch
(commits `81c1d55`, `02456c9`, `0d1da92`, `0bdfe80`, `85b2ac1`,
all wiped via the `cd4cea4` reset that preceded this redemption)
was caught by `pre_geometric/lean_repo_audit/per_branch_audit.md`
with three specific charges:

1. **Build broken**: `HypothesisSet.lean` and
   `SpectralOperations.lean` were imported by every other module
   *but never committed to the branch*.  `lake build` would have
   failed on the branch as published.

2. **STATUS.md falsely claimed green**: the prior STATUS asserted
   "0 sorries, 0 True placeholders, 5 named axioms" and a green
   build, with no acknowledgement that the build actually fails.

3. **Axiom-smuggling**: the headline
   `composition_unique_under_three_conditions` rested on
   `three_conditions_force_higher_moments` — an axiom asserting
   *exactly the conclusion* that any three-condition operation
   matches additive convolution on every moment.  The "citation"
   to Reed-Simon I §VIII.33 was misleading: Reed-Simon proves
   commutativity of additive lifts; it does not assert that all
   three-condition operations admit such a lift.

This branch:

| Charge | Prior branch | This redemption |
|---|---|---|
| HypothesisSet.lean committed? | **No** (imported but missing) | **Yes** (`git ls-tree HEAD` shows file present) |
| SpectralOperations.lean committed? | **No** (imported but missing) | **Yes** |
| Build state | Would fail | **Passes** (`lake build SpectralPhysics` succeeds in 3179 jobs) |
| STATUS.md honesty | Claimed green falsely | This file; 4 scopes labelled CLOSED/CONDITIONAL/OPEN |
| Broader uniqueness | "Proved" via smuggled axiom | Recorded as `PointwiseUniqueness` predicate; NOT proved, NOT axiomatised |
| Axioms with conclusion content | `three_conditions_force_higher_moments` (= conclusion) | None.  K1+K2+K3 are *forward* shadow of Mesland-Rennie / RS / Kassel; Minkowski-cancel axioms are generic facts about multisets |
| `#print axioms` audit | Would expose the smuggling | Clean — see §6 |

This redemption mirrors the discipline of
`compute/self-model-deficit-rigorous`:

* Open content lives in **predicate hypotheses**, not in axioms
  and not in `sorry`.
* Each named axiom is a **generic external fact** with explicit
  paper citation, not the conclusion of any in-branch theorem.
* The STATUS file maps each headline theorem to its precise
  axiom dependency.

---

## 6. Build status

```
$ lake build SpectralPhysics
... (full build; warnings inherited from unrelated `Conjectures/`
     files only — no errors in CompositionUniqueness/) ...
✔ [3178/3179] Built SpectralPhysics (2.1s)
Build completed successfully (3179 jobs).
```

### `#print axioms` for the headline theorems

```
'additive_is_unique_among_three_named' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   minkowski_left_cancel, minkowski_right_cancel]

'three_conditions_force_trace_law' depends on axioms:
  [propext, Classical.choice, Quot.sound]
  -- ZERO non-kernel axioms

'kasparov_three_conditions' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   K1_mesland_rennie_card, K2_rosenberg_schochet_cancel,
   K3_kassel_residue]

'kasparov_product_trace_eq_additive' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   K3_kassel_residue]
  -- only K3 needed for the trace channel

'composition_unique_conditional_on_broader' depends on axioms:
  [propext, Classical.choice, Quot.sound]
  -- ZERO non-kernel axioms — the broader uniqueness is a
  -- HYPOTHESIS, not an axiom

'additive_satisfies_three_conditions' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   minkowski_left_cancel, minkowski_right_cancel]
```

The Scope-2 trace channel and the Scope-4 conditional form
**depend on zero non-kernel axioms**.  The other theorems'
axiom dependencies are limited to the five literature-cited
axioms documented in §2.

---

## 7. Honest verdict

**Does this close the v0.9 line 16783 admission rigorously?**
Partially.

**Which parts are closed?**

* The **trace-channel** form is closed unconditionally (Scope 2).
  This is the part needed for downstream physics: partition
  functions, mass-trace sums, thermodynamic potentials all
  factor through the trace.  The trace functional of any
  three-condition operation IS that of additive convolution.

* The **Kasparov-product** form is closed conditional on K1+K2+K3
  (Scope 3).  This is exactly Path A: within the category of
  spectral triples used by the v0.9 framework's downstream
  physics (Connes-Chamseddine spine, Chapters 13–14), the
  uniqueness claim is settled by Mesland-Rennie 2014/2016 +
  Rosenberg-Schochet 1987 + Kassel 1986.

* The **named-candidates** form is closed (Scope 1) modulo the
  Minkowski-cancellation axioms.

**What stays open?**

* The **broader pointwise** claim — that *every* binary operation
  on `Spectrum` satisfying the three conditions equals
  `additiveConv` pointwise — is recorded as the
  `PointwiseUniqueness` predicate in `BroaderUniquenessOpen.lean`.
  It is NOT proved.  It is NOT axiomatised.  Per Path A this is
  a v1.0 NCG-extension target.

**Comparison to the prior deceptive version.**  The crucial
structural difference: in the prior branch, the broader pointwise
claim was made to *appear* proved by axiomatising precisely the
content needed to make it follow.  In this branch, the broader
claim sits as a `Prop` that downstream callers must assume as a
hypothesis if they need it.  The audit-discipline catches this
explicitly: `#print axioms` on the Scope-4 conditional form shows
**zero** non-kernel axioms; the hypothesis is openly there.

**Is this useful as a partial result?**  Yes:

1. The trace-channel result (Scope 2) covers all downstream
   physical predictions that depend on the trace.
2. The Kasparov-product narrow result (Scope 3) covers the
   load-bearing v0.9 sites at lines 5443 (norm-multiplicativity),
   6013 (τ = 1/(2+φ)), and 6632 (Connes M×F spectral triple) —
   all of which live in the Kasparov-product spectral category.
3. The honest open status of the broader pointwise claim closes
   the v0.9 line 16783 admission *in the only way that does not
   axiom-smuggle*: by recording it as an open problem at the
   right place in the type theory.

**A future "fully closing" branch** would need to either:

(a) Prove `PointwiseUniqueness` from a strengthened spectrum-level
hypothesis (e.g., a Lean-level formulation of the multiset moment
problem) without axiomatising the conclusion.  This would require
porting Shohat-Tamarkin / Akhiezer determinacy theory into
Mathlib at the `Multiset ℝ` level, which is itself a substantial
mathematical formalisation project.

(b) Formalise unbounded KK-theory in Mathlib and obtain
K1+K2+K3 as proved theorems rather than named axioms.  This is
the largest of the three "next steps" and is on the order of
porting `Mathlib.Analysis.NormedSpace.OperatorAlgebras` for which
infrastructure does not yet exist.

Neither (a) nor (b) is in this branch.  Neither is pretended.

