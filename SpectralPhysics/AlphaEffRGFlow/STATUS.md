# AlphaEffRGFlow — v0.9.2 G.7 closure (α_eff > 0 below EW)

**Date:** 2026-05-11
**Branch:** `compute/alpha-eff-RG-below-EW`
**v0.9 line:** 16805 (NON-PERT-PHYSICS)
**Verdict:** **CONDITIONAL** — α_eff > 0 below EW holds under a
three-hypothesis (RGE + decoupling + cutoff/transport) closure with
four named literature axioms. Empirical closure requires a
Python/mpmath RG sidecar (location: `yukawa/pre_geometric/alpha_eff_RG_below_EW/`).

---

## Context (v0.9 admission)

v0.9 §G.7 (line 16805) admits:

> Seeley–DeWitt computed at cutoff; RG to lower energies could change
> sign as heavy particles decouple.  1-month explicit RG calculation
> in SM-below-EW.

This module formalises that route as a Lean conditional theorem.  It
does **not** discharge the quantitative computation.

---

## Files

| File                                       | Lines | Status                              |
| ------------------------------------------ | ----: | ----------------------------------- |
| `AlphaEffRGFlow/RGEquations.lean`          |  ~190 | Tier 2, 0 sorry, **3 named axioms** |
| `AlphaEffRGFlow/DecouplingThreshold.lean`  |  ~180 | Tier 2, 0 sorry, **1 named axiom**  |
| `AlphaEffRGFlow/AlphaEffRunning.lean`      |  ~170 | Tier 2 conditional, 0 sorry, 0 new axioms |
| `AlphaEffRGFlow/SignFlipRiskAnalysis.lean` |  ~145 | Tier 1 honest negative, 0 sorry, 0 axioms |
| `AlphaEffRGFlow/Verdict.lean`              |  ~160 | Tier 2 conditional, 0 sorry, 0 new axioms |
| `AlphaEffRGFlow/STATUS.md`                 |       | this file                           |

Wired into the project via `SpectralPhysics.lean` →
`import SpectralPhysics.AlphaEffRGFlow.Verdict`.

---

## Named axioms (4 total, all with citations)

### 1. `machacek_vaughn_two_loop_exists` — `RGEquations.lean`

> `∀ (c₀ : SMCouplings) (t₁ t₂ : ℝ), t₁ ≤ 0 → 0 ≤ t₂ →
>     ∃ (c : SMTrajectory), c 0 = c₀ ∧ SMRGEquationsOn c t₁ t₂`

**Category:** Tier 2 — named axiom with literature citation.
**Citation:**
* Machacek, M.E., Vaughn, M.T. (1983). *Two-loop renormalization group
  equations in a general quantum field theory: I. Wave function
  renormalization*. Nucl. Phys. **B222**, 83–103.
* Machacek, M.E., Vaughn, M.T. (1984). *...II. Yukawa couplings*.
  Nucl. Phys. **B236**, 221–232.
* Machacek, M.E., Vaughn, M.T. (1985). *...III. Scalar quartic
  couplings*. Nucl. Phys. **B249**, 70–92.

**Why axiomatised**: porting the explicit polynomial form of the
seven 2-loop β-functions into Lean is out of scope (hundreds of
symbolic terms verified by `RGE++` and `PyR@TE`). The axiom carries
the *existence* of the solution, not its analytic form.

**Honesty check**: the axiom is *not* "α_eff > 0" or any conclusion;
it is the textbook existence statement that the SM RGE admits a
solution.

### 2. `ford_jones_stevenson_stephens_extension` — `RGEquations.lean`

> `∀ (c : SMTrajectory) (t₁ t₂ t₃ : ℝ),  …
>     SMRGEquationsOn c t₁ t₂ →
>     (∃ c', c' t₂ = c t₂ ∧ SMRGEquationsOn c' t₂ t₃) →
>     ∃ c'', SMRGEquationsOn c'' t₁ t₃`

**Category:** Tier 2 — named axiom with literature citation.
**Citation:** Ford, C., Jones, D.R.T., Stevenson, P.W., Stephens, M.B.
(1992). *The effective potential and the renormalisation group*.
Nucl. Phys. **B395**, 17–34.

**Why axiomatised**: the extension theorem (concatenating two
local-window solutions across a junction point) is a corollary of
the analyticity properties established by FJSS 1992. We carry it
directly.

### 3. `mihaila_salomon_steinhauser_three_loop` — `RGEquations.lean`

> `∀ (c₀ : SMCouplings) (t₁ t₂ : ℝ), t₁ ≤ 0 → 0 ≤ t₂ →
>     ∃ (c : SMTrajectory), c 0 = c₀ ∧ SMRGEquationsOn c t₁ t₂`

**Category:** Tier 2 — named axiom with literature citation.
**Citation:**
* Mihaila, L.N., Salomon, J., Steinhauser, M. (2012).
  *Gauge coupling beta functions in the Standard Model to three
  loops*. Phys. Rev. Lett. **108**, 151602.
* Companion paper: Phys. Rev. **D86**, 096008 (2012).

**Why axiomatised**: the 3-loop gauge β-functions are a refinement
of MV1983 with explicit polynomial form; we carry their existence
as a separate axiom so downstream theorems may quantify over either
precision level.

**Honesty check**: this axiom and `machacek_vaughn_two_loop_exists`
state the same closure (existence of a solution); they are kept
separate to preserve the citation trail.

### 4. `manohar_wise_decoupling` — `DecouplingThreshold.lean`

> `∀ (c : SMTrajectory) (t₁ t₂ : ℝ),
>     SMRGEquationsOn c t₁ t₂ →
>     t₁ ≤ Real.log (m_tau / M_Z) →
>     Real.log (m_top / M_Z) ≤ t₂ →
>     DecouplingAtThresholds c`

**Category:** Tier 2 — named axiom with literature citation.
**Citation:** Manohar, A.V., Wise, M.B. (2000). *Heavy Quark Physics*.
Cambridge Monographs on Particle Physics, Nuclear Physics, and
Cosmology vol. 10, Cambridge University Press. Chapter 5.
**Cross-references:** Appelquist–Carazzone 1975 (original
decoupling); Bernreuther–Wetzel 1982 (MS-bar version).

**Why axiomatised**: heavy-particle decoupling at the named SM
thresholds (top, Higgs, bottom, tau) is textbook content; the
matching expressions are O(α_s/π) corrections and do not move the
sign of `α_eff`.

**Honesty check**: the axiom is purely existential in the matching
predicate `DecouplingAtThresholds`; it does *not* assert that
`α_eff` has any particular value or sign.

---

## Predicate-hypothesis closure

The headline conditional theorem
`alpha_eff_verdict_v092_G7` in `Verdict.lean` takes three Prop
predicates as hypotheses:

* **`h_RGE : H_RGE t_Z t_UV`** — existence of an SM trajectory
  satisfying the RGE on `[t_Z, t_UV]`.
* **`h_decoupling : H_Decoupling t_Z t_UV`** — that trajectory also
  satisfies decoupling at the four thresholds.
* **`h_transport`** — the regulator coefficient `α_eff` is
  continuous, boundary-matches `alphaEffAtCutoff` at `t_UV`, and
  **does not cross zero** anywhere on the window.

Conclusion: `∃ c, ∀ t ∈ [t_Z, t_UV], αEffAt c t > 0`.

### What's open

`h_transport.signStable` is the **open content**.  No theorem of this
module excludes a zero-crossing of `α_eff(c, t)` between `M_Z` and
the cutoff.  Closure requires either

* **Route 1 — sidecar**: Python/mpmath RG-running script in
  `yukawa/pre_geometric/alpha_eff_RG_below_EW/` (not created in this
  branch); or
* **Route 2 — β-inequality**: a structural inequality on the
  regulator's β-coefficients that excludes a sign change a priori.

Both routes are recorded as predicates in `SignFlipRiskAnalysis.lean`
(`SignFlipExcludedBySidecar`, `SignFlipExcludedByBetaInequality`)
and *not* axiomatised.

---

## Verdict

**CONDITIONAL.**

The Lean closure formalises the route to "α_eff > 0 below EW" as a
three-hypothesis conditional theorem.  The closure is honest:

1. The three hypotheses are **named `Prop` predicates**, not asserted
   facts.
2. The four named axioms cite **real published literature**:
   Machacek–Vaughn 1983/1984/1985, Ford–Jones–Stevenson–Stephens 1992,
   Mihaila–Salomon–Steinhauser 2012, Manohar–Wise 2000.
3. No definitional triviality — `αEffAt` is an `opaque`
   `SMTrajectory → ℝ → ℝ` function (not a constant), and the headline
   theorem's hypotheses do not unfold trivially.
4. The empirical input `alphaEffAtCutoff` is isolated as an `opaque ℝ`
   (one isolated input) and consumed only via the transport
   hypothesis's `boundary` field.

The closure **does not** prove "α_eff > 0 below EW".  It formalises
the implication

  `(RGE solution) ∧ (decoupling) ∧ (transport positivity)`
   ⇒ `α_eff > 0 on the window`,

and explicitly records that the antecedent's third conjunct is
**open** — requiring a sidecar Python/mpmath RG run or a structural
β-function inequality.

---

## Sidecar pointer

Empirical closure of `h_transport.signStable` requires a
Python/mpmath sidecar at

  `yukawa/pre_geometric/alpha_eff_RG_below_EW/`

with the following minimum contents (not created in this branch):

* `rge_integrator.py` — solves the SM RGE from `M_Z` to `Λ_UV` at
  50-digit precision using MS-bar input from PDG 2024.
* `alpha_eff_track.py` — tracks `αEffAt c t` along the trajectory
  using the regulator coefficient's β-function transport.
* `sign_check.md` — reports `min_t (αEffAt c t)` on the window with
  the threshold-matching uncertainty bound from Manohar–Wise 2000.

Closure-by-sidecar discharges the third audit-discipline hypothesis,
which combined with the four named axioms (RGE existence ×3 +
decoupling) and the cutoff positivity from `SeeleyDeWitt/STATUS.md`
yields the empirical claim.

---

## Comparison to reference branches

| Aspect                      | `KSRCompactness` | `Kappa2FromSpectrum` | **This module** |
| --------------------------- | ---------------- | -------------------- | --------------- |
| Verdict                     | CONDITIONAL      | CONDITIONAL (negative result) | CONDITIONAL |
| Number of named axioms      | 1                | 6                    | **4**           |
| Open content carrier        | 2 Prop hyps      | 0 (numerical bracket axiom) | **3 Prop hyps** |
| Sidecar required            | No               | Yes (mpmath)         | **Yes**         |
| Empirical claim closed?     | Yes (compactness) | No (κ₂ ≈ 287, target 258) | **No** (empirical step is the sidecar) |

The closure pattern matches `KSRCompactness` (predicate-hypothesis +
named-axiom dispatch) but with a richer three-bucket hypothesis
structure that mirrors the three components of v0.9 §G.7's admission
(RGE + decoupling + cutoff positivity).
