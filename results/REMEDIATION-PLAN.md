# Remediation Plan — Lean ↔ Manuscript "one true story"

**Date:** 2026-05-27. Inputs: `results/ALIGNMENT-GAP-REGISTER.md`, `results/AXIOM-SOUNDNESS-SWEEP.md`.
Goal: Lean and manuscript tell one true story — advance Lean where it lags (Category A), revise the
manuscript down where Lean exposes a defect (Category B), and **fix the unsound axioms first**.

## P0 — Soundness (release-blocking; gates everything)
The repo has **4 unsound axioms** (same class: a bound/equality over an under-constrained quantified
variable/structure). Until fixed, any result resting on them is logically void.
1. Fix by restricting the bounded variable to its realisable domain:
   - `BekensteinInformationBound` / `NaturalityCoherence` (`SelfModelDeficitUnconditional`) — quantify over the
     actual information content (`negZetaPrimeAtZero V`), not all `c:ℝ`.
   - `cheeger_lower` / `cheeger_upper` (`Analysis/CheegerInequality.lean`) — add a `CheegerData` invariant
     encoding the real graph relationship, or quantify over actual graph Laplacians.
2. Re-verify: `False` no longer derivable; rebuild; `#print axioms` on the `SelfModelDeficitUnconditional` family.
3. Convert the 2 redundant axioms (`aps_bismut_freed_majorana_doubling`, `seesaw_product_independence`) to theorems.
4. Guardrail: extend `scripts/check_axioms.sh` to flag the new class (axiom whose type is a bound/equality over a
   free numeric var / unconstrained structure). This is the bug 3 audits missed.

**Blast radius:** Bekenstein+Naturality contaminate the live `SelfModelDeficitUnconditional` `=288` family
(root build). Cheeger axioms are unsound-but-unused (latent landmines).

## P1 — Manuscript honesty (parallel with P2)
Revise the headline Category-B queue so tier labels match what Lean establishes — *down*, never by
re-introducing the defect:
- Koide K=2/3 → Tier-2 conditional on `ε²=2` (admitted fit); Lean unproved.
- κ₂/CC magnitude → not predicted (tuned to Λ_obs); split OP21 (visible=A, hidden=B).
- "288" see-saw → keep OPEN (don't present the back-fit as closure).
- Σmν → "one route + kinematic floor"; drop "two independent routes."
- A_s → structural-factor result, not an A_s closure.
- σ₀/M_Pl → drop the Hodge "closure" of the manuscript's own superseded claim.
- Tautology/shell theorems (SU(2) `12/7`, `SpectralArithmetic` monograph shells, Baker existentials) → relabel placeholders.

## P2 — Advance Lean (genuine Category-A lags)
Courant-Fischer min-max, DiscreteCheeger (co-area), the Tier-1 σ₀/M_Pl algebra, Newton-Girard, ℝ⁴ QFT
continuum (Mathlib-limited; may stay open). Real work, not integrity issues — lowest urgency.

## P3 — Protect the clean core
Cabibbo, θ₁₃, η_B(λ¹⁴), Σmν floor, cosmic budget/w(z)/Hubble, Gödel trace, Cayley-Dickson, **all of
QFT/Yang–Mills** (manuscript honest) — confirmed clean. Keep green; guard with the P0 CI check.

## Sequencing
P0 → then P1 ∥ P2; P3 is maintenance. P0 is the gate.

---

## P4 — Obligations queued from research passes (append-only; newest first)

Forward obligations named by a research pass and gated by Aaron. Distinct from P0–P3, which
remediate existing defects. Format: `obligation — shape — why it is worth Lean time — source`.

### 2026-08-26 — birth-of-geometry × wave-trace keystone decomposition (Aaron D5)
Source: `~/ember-review/artifacts-2026-08-24/BOG-WAVETRACE-THEOREMS-2026-08-25.md` §5; review
`~/ember-review/REVIEW-2026-08-25-bog-wavetrace-keystone.md`.

- **C5(a)–(e) — PRIORITY.** Finite-dimensional Clifford algebra + parity (`Mathlib.LinearAlgebra.
  CliffordAlgebra`, `Matrix.trace`). The first sub-principal wave invariant of the framework
  operator is **even** w.r.t. `γ₅ ⊗ γ_F`, so the unweighted trace is parity-blind at that order.
  *Why:* it is the cheapest item on this list **and** it converts the odd-selector statement from
  a hunch into a theorem — the named object the axiom-3 / arrow / Yukawa threads all converge on.
- C3(a) lattice characterization; C3(b) two-sided bound — finite sums.
- C4(a) multiplicativity + triad value; C4(b) gradient formula and critical set — entropy gradient.
- C4(c) shift-freedom ODE.
- C2(b) — the finite-dimensional counterexamples to ζ-factorization; trivial to formalize as
  witnesses. (The manuscript statement they refute was corrected 2026-08-26.)

**Not Lean targets:** C1(b) is T1 *modulo a citation* (Hörmander 1968, scalar-phase FIO), not a
formalization gap. C1(b′) on general M is the one literature-conditional item (nonzero-period
Dirac trace formula, Jakobson–Strohmaier) — it stays a citation obligation, not a proof target.
