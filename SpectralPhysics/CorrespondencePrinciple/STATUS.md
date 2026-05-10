# compute/correspondence-principle-monotonicity — STATUS

## Branch
`compute/correspondence-principle-monotonicity` (off `master`).

## Verdict
**CO-MONOTONE.** Across the v0.9 acceptance window
M_R ∈ [3·10¹⁴, 1.5·10¹⁵] GeV, the IR-dominant Hessian eigenvalue
`Hess_min(M_R)` and the spectral gap `λ_1(M_R)` are strictly
co-monotone. The full numerical sweep (21 log-uniform points in the
window plus an 8-point cross-check spanning [10¹³, 10¹⁷] GeV) shows
`d ln(Hess_min)/d ln(M_R) = d ln(λ_1)/d ln(M_R)` to mpmath dps=50,
with the ratio of forward differences fixed at 1.0000.

The mechanism: `Hess_min = λ_1 · (c₁ f₂ Λ_c² − 6 f₀ α_eff λ_1)` is in
the *linear regime* throughout the window, since
`λ_1 / (c₁ f₂ Λ_c² / 6 f₀ α_eff) ∼ 10⁻¹²⁰ ≪ 1`. The slope of the map
`λ_1 ↦ Hess_min` at `λ_1 = 0` is `c₁ f₂ Λ_c² ≈ 0.0245` (M_Pl² units).

## Files

### Python (`yukawa/pre_geometric/correspondence_monotonicity/`)
* `hess_lambda1_sweep.py` — numerical sweep at mpmath dps=50
* `results.json` — tabulated values
* `console_output.txt` — verbose log
* `monotonicity_check.md` — analysis writeup

### Lean (`SpectralPhysics/CorrespondencePrinciple/`)
* `HessLambda1Monotonicity.lean` — formal monotonicity statement and
  proof (no sorries, no True placeholders)
* `Verdict.lean` — verdict + correspondence-principle selection
  corollary (no sorries)
* `STATUS.md` — this file

## Lean theorems

In `HessLambda1Monotonicity.lean`:
* `c1RouteB_pos`, `f0_pos`, `f2_pos`, `alphaEff_pos`,
  `lambdaCSq_pos`, `xiCrossSq_pos` — positivity of primitives
* `hessMin_zero` — `Hess_min(0) = 0`
* `hessMin_pos_in_window` — `Hess_min > 0` for `0 < λ_1 < ξ_cross²`
* `hessMin_strictMono_below_peak` — strict monotonicity of
  `λ_1 ↦ Hess_min` on `(0, ξ_cross²/2)`
* `hess_lambda1_co_monotone` — **headline**: any two points in the
  window satisfying `λ_1(M_R) < λ_1(M_R')` give
  `Hess_min(M_R) < Hess_min(M_R')`
* `hess_lambda1_eq_of_eq` — symmetric form
* `window_co_monotone` — concrete corollary instantiated at the
  axiomatised `window_gap_map`

In `Verdict.lean`:
* `MonotonicityVerdict` (inductive: coMonotone | counterMonotone | nonMonotone)
* `windowVerdict := coMonotone`
* `windowVerdict_eq_coMonotone : windowVerdict = coMonotone`
* `verdict_co_monotone` — full quantification
* `correspondence_principle_selects_min_lambda1` — the
  selection-criterion statement
* `correspondence_principle_consistent_with_obs` — qualitative
  alignment with Λ_obs

## Sorrys
**None.**

## True placeholders
**None.**

## Named axioms
1. `window_gap_map : WindowGapMap` (in
   `HessLambda1Monotonicity.lean`)

   Witnesses the existence of the function `M_R ↦ λ_1(M_R)` on the
   v0.9 window with `0 < λ_1(M_R) < ξ_cross²/2`. The structural
   identity `λ_1 = exp(−κ_2/2)·Λ_c²` and the SCSE bisection that
   computes κ_2(M_R) are not formalised here; they live in the
   Python sweep at `hess_lambda1_sweep.py`. The numerical bound
   `λ_1 ∈ [10⁻¹²⁸, 10⁻¹¹⁸]` for `M_R ∈ [3e14, 1.5e15]` GeV is far
   below the `ξ_cross²/2 ≈ 1.09e−2` threshold (over 100 orders of
   magnitude headroom), so the existence assumption is empirically
   well-grounded.

   No PDG, Planck, or other external numerical inputs feed this
   axiom — the sweep uses only framework primitives plus the
   structural identity.

## Build status
* `lake build SpectralPhysics.CorrespondencePrinciple.HessLambda1Monotonicity`
  — succeeds, 2178 jobs, no errors
* `lake build SpectralPhysics.CorrespondencePrinciple.Verdict`
  — succeeds, 2179 jobs, no errors
* `lake build` (full) — succeeds, 3173/3173 jobs

## Implications for v1.0 standing claim

### Sign-flip possibility
With the σ_tr anti-diffusive sign convention of
`SigmaTrDispersion.lean` (Whitt 1984; σ_tr > 0 below crossover ↔
*unstable* trace-mode direction), Samuelson's correspondence
principle selects the SAGF critical point with the **smallest**
`Hess_min`. By the co-monotonicity theorem, this is the critical
point with the **smallest** `λ_1`. This is **sign-flipped from
v0.9's stated SGM** ("largest λ_1") and **empirically aligned**
with Λ_obs ≈ 10⁻¹²² being the smallest λ_1 produced by the SCSE
in the M_R window.

### Sign-of-sign caveat
The conclusion above depends on whether σ_tr > 0 means
"anti-diffusive / unstable" (Whitt convention, used in
`SigmaTrDispersion.lean`) or "diffusive / stable" (alternative
literature convention). Under the latter, the conclusion flips
back to "largest λ_1", consistent with v0.9's stated SGM.

### Consequence for the IRREDUCIBLE+REFINED verdict
The IRREDUCIBLE+REFINED verdict in
`pre_geometric/economics_tools_for_SGM/verdict.md` treated SGM as
"the 4th irreducible structural commitment, best absorbed into the
strong form of Axiom 3". This calculation reveals a more
optimistic possibility:

> Under the framework's preferred σ_tr sign convention, SGM is
> **derivable** as a theorem (correspondence principle + 
> co-monotonicity) — but with sign **flipped** from v0.9's
> stated form: select smallest λ_1, not largest.

Whether to:
(a) accept the sign-flipped reading (Route A re-opens; SGM
    becomes a theorem; v0.9 narrative needs minor reworking);
(b) preserve v0.9's stated SGM and treat the σ_tr sign convention
    as the open question;
(c) keep the IRREDUCIBLE+REFINED reading (SGM as strong-Axiom-3)
    and treat correspondence-principle as a side benefit;

is a manuscript-level decision, not a calculational one. The
calculational fact — co-monotonicity — is established here.

### What the next dispatch should consider
1. Re-examine `pre_geometric/c1_and_5sector/verdict.md` to confirm
   which σ_tr sign convention is genuinely the framework's.
2. If anti-diffusive (Whitt) is correct, draft a manuscript
   amendment promoting SGM to a theorem of "self-referential
   capacity ↔ smallest λ_1 critical point".
3. If diffusive (Codello-Percacci) is correct, re-state the
   IRREDUCIBLE+REFINED verdict as standing.
4. Either way, this branch's Lean theorems are useful: they
   formalise the co-monotonicity that lets the
   correspondence-principle reading even be discussed.

## Hard rules compliance
- [x] No sorrys
- [x] No `True` placeholders
- [x] Lean build compiles (full `lake build` clean)
- [x] Branch correct (`compute/correspondence-principle-monotonicity`)
- [x] No push to remote
- [x] Honest verdict (CO-MONOTONE reported as computed; sign-of-σ_tr
      caveat flagged explicitly)
- [x] Python computation in
      `yukawa/pre_geometric/correspondence_monotonicity/`
- [x] Lean axiom (`window_gap_map`) cites the Python computation
