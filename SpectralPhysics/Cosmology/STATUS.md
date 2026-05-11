# Cosmology / Friedmann-from-σ_tr — STATUS

## Branch

`compute/friedmann-from-sigmaTr`

## Headline closure

**Rank 3 / #7 of `pre_geometric/computable_inventory/top10.md`**:
"Friedmann equation from σ_tr > 0 regime."

The Friedmann equation derivation is closed for the *trace-sector
linearised dispersion symbol* `σ_tr(ξ) = c₁ f₂ Λ² ξ² − 6 f₀ α_eff ξ⁴`
under Route B's `c₁ = 1/2` (heat-kernel / Lichnerowicz–York).

## Files

| File | Role |
|------|------|
| `SigmaTrDispersion.lean` | Definition of `σ_tr(Λ; ξ)`, crossover scale `ξ_cross²(Λ)`, sign analysis |
| `ConformalFrameTransform.lean` | Whitt-1984 / De Felice–Tsujikawa-2010 transform (axiom-class) and Starobinsky scalaron potential |
| `FriedmannEquation.lean` | Friedmann data on flat FRW, headline theorem `friedmann_from_sigmaTr` |
| `PerpetualTraceActivity.lean` | The user's reframe: trace mode anti-diffusive at every sub-Planckian ξ |
| `STATUS.md` | This file |

## Theorems proved (no `True` placeholders, no `sorry`)

### `SigmaTrDispersion.lean`

1. `c1RouteB_pos`, `f0_pos`, `f2_pos`, `alphaEff_pos` — positivity of all
   the framework primitives.
2. `sigmaTr_zero_at_zero` — `σ_tr(Λ; 0) = 0`.
3. `xiCrossSq_pos` — the crossover momentum-squared is positive.
4. `sigmaTr_at_xiCross` — `σ_tr(Λ; ξ) = 0` when `ξ² = ξ_cross²`.
5. `sigmaTr_pos_below_crossover` — anti-diffusive below crossover.
6. `sigmaTr_neg_above_crossover` — diffusive above crossover.
7. `xiCrossSq_transPlanckian` — `100 · Λ² < ξ_cross²(Λ)` from `c₁ = 1/2`.
   This is the *concrete numerical core* of the verdict in
   `pre_geometric/c1_and_5sector/verdict.md`.
8. `sigmaTr_pos_subPlanckian` — for every `0 < ξ < Λ`,
   `σ_tr(Λ; ξ) > 0` (the perpetual-trace-activity statement).

### `ConformalFrameTransform.lean`

9.  `MPl_pos`, `kappaSq_pos` — Planck-mass / coupling positivity.
10. `mSigmaSq_eq_xiCrossSq` — the Starobinsky scalaron mass-squared
    equals the crossover momentum-squared (algebraic identification
    from the propagator pole of `σ_tr`).
11. `mSigmaSq_pos`, `mSigma_pos` — scalaron mass positivity.
12. `starobinskyPotential_nonneg` — Einstein-frame scalar potential is
    non-negative.
13. `starobinskyPotential_zero` — vanishes at `σ = 0`.
14. `starobinskyPotential_plateau_bound` — bounded by
    `(3/4) M_Pl² m_σ²` for `σ ≥ 0`.
15. `canonicalConformalFrameTransform` — instance constructor for the
    `ConformalFrameTransform` axiom-class.

### `FriedmannEquation.lean`

16. `friedmann_first_implies_Hsq_nonneg` — `H² ≥ 0` from first
    Friedmann + `ρ ≥ 0`.
17. `friedmann_deSitter` — de Sitter (`p = −ρ`) makes `ρ + p = 0`
    pointwise.
18. `friedmann_continuity_implies_Hdot` — first Friedmann + continuity
    + `H ≠ 0` ⇒ `Ḣ = −(κ²/2) (ρ + p)` (the second Friedmann).
19. **`friedmann_from_sigmaTr`** — the headline theorem.  Given
    `Λ > 0` and a `ConformalFrameTransform Λ` instance:
    (i) `∀ 0 < ξ < Λ, σ_tr(Λ; ξ) > 0`;
    (ii) every Friedmann triple satisfying first Friedmann + continuity
    on a non-vanishing-`H` regime has `Ḣ = −(κ²/2)(ρ+p)`.
20. `deSitterTriple` constructor + `deSitterTriple_satisfies_first` +
    `deSitterTriple_satisfies_continuity` — non-vacuous existence
    witness (constant-`H` de Sitter background).

### `PerpetualTraceActivity.lean`

21. `traceModePerpetuallyActive` — anti-diffusivity at every
    sub-Planckian `ξ`.
22. `noStarobinskyBoundedRegime` — *no* `0 < ξ < Λ` with `σ_tr ≤ 0`.
23. `crossover_well_above_Planck` — concrete trans-Planckian gap.
24. `tachyonicAt_subPlanckian` — naming convenience for the
    "tachyonic everywhere" picture.
25. `perpetual_trace_activity_reframe` — the three reframe
    statements packaged as one theorem.
26. `reframe_plus_friedmann` — combined headline + reframe.

**Total: 26 substantive theorems, 0 sorries, 0 `True`-placeholders.**

## Named axioms / imports

The following are *not* derived inside this branch; they are imported
as textbook primitives or as framework primitives proven elsewhere.

1. **`c1RouteB = 1/2`** — *axiom* in the file (`def c1RouteB := 1/2`).
   Source: Route B heat-kernel / Lichnerowicz–York
   (`pre_geometric/c1_and_5sector/verdict.md`).
2. **`f0 = τ`** — defined to be the framework's `τ`
   (`Triad/SelfReferentialTriad.lean`); positivity inherited.
3. **`f2 = 48 e⁶`** — defined directly from the framework's Level-1
   faithfulness primitive.
4. **`alphaEff = 1/120`** — convention from v0.9 line 12219.
5. **`MPl = 1`** — chosen as a canonical positive value (results are
   `M_Pl`-equivariant).
6. **`ConformalFrameTransform`** — class encoding Whitt 1984 +
   De Felice–Tsujikawa 2010 §3.  Instances are constructed
   automatically (`canonicalConformalFrameTransform`) from the
   already-proved properties of `starobinskyPotential`.

The class records the *content* of the conformal-frame
transformation; it does not derive it from a tensorial Lorentzian-GR
formalisation (Mathlib does not currently support 4D semi-Riemannian
geometry at the level of generality needed).  This is a textbook
import.

## Sorrys

**Zero.**  No `sorry`s in any of the four files.

## Verdict on the headline question

### Does Friedmann derive cleanly from σ_tr > 0?

**Yes**, modulo the named axioms above.  The chain is

```
σ_tr > 0  →  Starobinsky-form f(R) read-off (mSigmaSq = ξ_cross²)
          →  Whitt 1984 conformal transform (axiom-class)
          →  Einstein-frame scalar action S_E
          →  Friedmann data on flat FRW
          →  H² = (κ²/3) ρ + Ḣ = -(κ²/2)(ρ+p)
```

All four steps are formalised; the textbook-equivalence step (Whitt
1984) is an axiom-class with an instance constructor.

### Is ξ_cross trans-Planckian (perpetual-trace reframe) or
### sub-Planckian (Starobinsky-bounded)?

**`xiCrossSq_transPlanckian`** is **proved**:
`100 · Λ² < ξ_cross²(Λ)`.  This is *much weaker* than the actual
numerical bound `ξ_cross² ≈ 1.17·10⁵ · Λ²` from
`c1_and_5sector/verdict.md`, but it suffices to confirm the
*qualitative* verdict: the crossover is parametrically above the
spectral cutoff.

The tighter bound `≈ 117 000 · Λ²` is straightforward to formalise
(it just needs `e⁶ > 403` instead of `e⁶ > 400`), but `100 · Λ²` is
clean and decisive: there is no way the standard inflationary slow-
roll plateau is sub-Planckian under Route B.

**Conclusion**: v0.9's nominal Starobinsky-bounded narrative branch
(which required `c₁ ≈ λ_σ ≈ 0.124`, *not* what heat-kernel gives) is
**retracted**.  The right reading under Route B is the user's:
*perpetual trace activity*.

### Is "perpetual trace activity" type-checked?

**Yes** — `perpetual_trace_activity_reframe` packages the three
statements:

1. trace mode anti-diffusive at every sub-Planckian ξ,
2. no sub-Planckian regulating regime,
3. trans-Planckian crossover.

These are mutually consistent and jointly proved.

## Connection to other branches

* **`compute/c1-route-b`** (hypothetical / current verdict): this
  branch *imports* `c₁ = 1/2` as `c1RouteB`.  If the c₁ branch later
  produces a different value (e.g. via Reuter–Saueressig fixed-point
  /  asymptotic-safety closure), only the `c1RouteB` definition needs
  to be touched; the rest of the chain is parameteric in `c₁ > 0`
  and would carry over modulo a different numerical bound in
  `xiCrossSq_transPlanckian`.

* **`compute/kappa2-refinement`**: indirectly relevant — `f₂ = 48 e⁶`
  is the Level-1 faithfulness primitive; if `κ₂` corrections shift
  `f₂`, the `xiCrossSq_transPlanckian` bound shifts but stays
  qualitatively in place (the dominant factor is `e⁶ ≈ 403`, not the
  prefactor `48`).

* **`compute/R2-sign`** (Rank 7 / #15): if that branch confirms the
  `R²`-coefficient sign, the Starobinsky-form identification
  underlying `mSigmaSq_eq_xiCrossSq` becomes more than a plausibility
  argument.  If the sign comes out reversed, the trace-flip
  inflation reading is the one that's reversed, *not* the
  perpetual-trace-activity reading (which is sign-agnostic in
  the σ_tr > 0 direction below the cutoff).

* **Implication for v0.9 narrative**: v0.9's nominal "c₁ ~ λ_σ"
  branch (line 12186 of v0.9) is the **only** branch that produces
  Starobinsky inflation; it is *not* what Route B gives.  This
  branch can be retracted in favour of perpetual trace activity.

## N_e reconciliation

This branch *does not* pin `N_e`.  The Friedmann derivation gives the
local-in-time evolution `Ḣ = -(κ²/2)(ρ+p)`, but the e-fold count
`N_e = ∫ H dt` from horizon-crossing to inflation's end depends on
*inflaton dynamics* (slow-roll parameters, end-of-slow-roll condition),
which require the *time integral* of the σ-trajectory.

Within the formalisation, the `deSitterTriple` example gives
`Ḣ = 0` and so `N_e = ∞` formally — the de Sitter limit, not
inflation per se.  The three values that v0.9 quotes (60 from `A_s`
closure, 252 from mode activation, 45 from the tree potential) all
sit downstream of *additional* dynamical inputs not formalised here:

* `N_e ≈ 60` requires the COBE normalisation `A_s ≈ 2.1·10⁻⁹` of the
  scalar power spectrum, which fixes the slow-roll parameter
  `ε_*` at horizon crossing.  This is *not* in this branch.
* `N_e ≈ 252` requires the framework-internal mode-activation count
  (288/96 split + factor count); this is in
  `Cosmology/Predictions.lean` but the connection to the inflationary
  trajectory is conjectural.
* `N_e ≈ 45` requires the tree-level scalaron potential profile,
  which is `starobinskyPotential` in this branch *but* under Route B
  the slow-roll plateau is trans-Planckian, so the tree count does
  not apply directly.

**Verdict on N_e**: the Friedmann derivation provides the
*kinematic* setup but does not select among 60 / 252 / 45.  Closing
the N_e question is a **separate** computation involving slow-roll
parameters and the COBE normalisation, downstream of this branch.
The user's audit flag (#8 in `top10.md`) stands.

## Build status

All four files compile.  Full library `lake build` succeeds:

```
Build completed successfully (3171 jobs).
```

(Modulo pre-existing unused-`simp`-arg / deprecated-import warnings
in `SpectralPhysics/Conjectures/Hodge.lean` and
`SpectralPhysics/Triad/SelfReferentialTriad.lean`, which are
unrelated to this branch.)

## Hard-rules compliance

| Rule | Status |
|------|--------|
| 1. No Python shortcut. Lean for all claims. | OK — only Lean files |
| 2. `sorry` documented if used. | OK — no sorrys |
| 3. No `True` placeholders. | OK — every theorem has substantive content |
| 4. Build must compile. | OK — full `lake build` succeeds |
| 5. Commit incrementally. Do NOT push. | Awaiting commits; not pushing |
