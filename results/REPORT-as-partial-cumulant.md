# REPORT — `spec:as-partial-cumulant`

**Task.** Make the `κ₂` law-of-total-variance cumulant mode-resolved and
truncatable; assemble `A_s = P·exp(−κ₂ᶦⁿᶠ/2)` and report it
parametrically. **Does NOT close `A_s`.**

**Repo / branch.** `Spectral-Physics-Lean` @ `feat/as-partial-cumulant`.
**Build.** `lake build` succeeds (3309 jobs). **New `sorry`: 0. New
`axiom`: 0.** (The two pre-existing `sorry`s live in
`SpectralPhysics/QFT/OSAxiom*.lean`, untouched by this work.)

**Files added/changed (surgical):**
- `SpectralPhysics/SelfModelDeficit/Kappa2Partial.lean` — **new**, the machine + assembly + brackets.
- `SpectralPhysics.lean` — **+3 lines** (one import, registering the new module).
- `results/as_transfer.md`, `results/REPORT-as-partial-cumulant.md` — **new**.

No closure theorem, trace-sector Lean, or manuscript file was modified.

---

## Headline: the full-spectrum anchor STOPs (Success-Criterion 7), honestly

The spec's required Task-1 anchor — `kappa2Partial univ ∈ (529.42, 529.43)`
from genuine **per-mode** `−log y_f` — **is not reconstructible from the
data the Lean repo contains, and was NOT forced.** Per the spec's own
Success-Criterion 7 ("STOP, do not force it, and report exactly where the
per-mode variance diverges") and `RIGOROUS_WORKFLOW.md` Rule 6 ("honest
negatives are first-class — PROVE the negative as a theorem"), the
divergence is formalized, not papered over.

**Where it diverges (proved, T1):**

| piece of `κ₂_full = 529.42` | value | per-mode grounded in repo? |
|---|---:|---|
| within-hidden `(N_hid/N)·κ₂_hid` | 400.19 | **yes** — see-saw cascade (§ below) |
| between-sector `B = (3/16)·26²` | 126.75 | **yes** — from the two sector means `μ_vis=6, μ_hid=32` |
| within-visible `(N_vis/N)·κ₂_vis` | **2.48** | **NO** — see below |
| **mode-grounded subtotal** | **526.94** | `kappa2_modeGrounded_bracket` ∈ (526.93, 526.95) |
| **full** | **529.42** | `kappa2_full` (existing) |

The single ungrounded piece is the **within-visible-Yukawa spread**
`κ₂_vis = 9.927069`. In the Lean repo the visible Yukawa coupling
`y : VisFermion → ℝ` is an **opaque `axiom`**; only PDG-cited **per-sector
sums** (`S_up = 97.23`, `S_down = 130.70`, `S_lep = 49.46`,
`S_νL = 184.62`) and the **aggregate** `κ₂_vis` exist. The per-sector sums
fix the visible **mean** (`μ_vis = 6`) but carry **no information about the
within-sector spread** — the individual `−log y_f` are absent. The Lean
theorem

```
kappa2_full_minus_modeGrounded :
    kappa2_full − kappa2_modeGrounded = kappa2_visible_spread   -- = 2.48
```

states the divergence as an exact identity, and `kappa2Partial_singleton`'s
`#print axioms` shows the only framework axiom in the per-mode chain is the
opaque `VisFermion.y` — confirming the gap is real, not an artifact.

This is exactly the outcome the spec's "Bonus value" note anticipated:
**`κ₂_vis` is an aggregate input not grounded in the per-mode Yukawas in
the Lean repo.** Surfacing it (rather than fetching PDG values and adding
12 new axioms to patch it, which the spec forbids) is the deliverable.

---

## What WAS built (all T1, zero `sorry`, zero new `axiom`)

### Task 1 — the mode-resolved machine + tests
- `pvar v S = (1/|S|)·Σ_{i∈S}(v i − mean_S v)²` — a genuine, truncatable
  population variance over an arbitrary mode set `S`.
- `kappa2Partial := pvar negLogY` over `VisFermion` (the index `ι` **already
  used** for the visible-sector distribution — not a new one).
- `kappa2Partial_empty : kappa2Partial ∅ = 0` ✓ (spec test).
- `kappa2Partial_singleton : kappa2Partial {a} = 0` ✓ (spec test, variance of one point).

### Task 1 — hidden sector reconstruction CONVERGES
- `cascadeVar_eq : cascadeVar a m = 2(m−a)²/3` — the see-saw cascade
  `(ξ_R, ξ_D, 2ξ_D−ξ_R)` is genuinely mode-resolvable in closed form
  (equal multiplicities ⇒ 288-mode variance = 3-point variance).
- `cascadeVar_reproduces_kappa2_hid : |cascadeVar ξ_R ξ_D − κ₂_hid| < 10⁻⁵`
  at the documented `ξ_R = 3.7090359, ξ_D = 32`. The hidden aggregate **is**
  grounded in its per-mode structure — the convergent half of the divergence.

### Task 2 — `A_s` assembly
- `AsValue P S = P·exp(−κ₂Partial(S)/2)`; `P` is an **input** (two-valued,
  `P₁ = 1.03·10⁻²` for `c₁=1`, `P₂ = 1.58·10⁻⁴` for `c₁=λ_σ`).
- `AsValue_full_is_CC_scale : log(AsTransfer P₁ κ₂_full) < −250` — at the
  **full** cumulant `A_s = P·exp(−264.71) ≈ 10⁻¹¹⁷`, CC-scale (vanishing).
  This proves the partial/full distinction is real: the full cumulant
  over-suppresses by ~100 orders, so `A_s` **requires** a partial cumulant.

### Task 3 — transfer function + honest report
- `AsTransfer P κ = P·exp(−κ/2)`; full table in `results/as_transfer.md`.
- `As_band_matching_kappa_inf` (Lean-proven brackets): `A_s ∈ [1.9,2.3]·10⁻⁹`
  for `κ₂ᶦⁿᶠ ∈ (22,24)` at `c₁=λ_σ` and `κ₂ᶦⁿᶠ ∈ (30,32)` at `c₁=1`.

---

## The band-matching `κ₂ᶦⁿᶠ` — a TARGET, not a result

> **`κ₂ᶦⁿᶠ ≈ 22.3 (c₁=λ_σ) … 31.0 (c₁=1)`** places `A_s` in the Planck band.

This range (matching the spec's expected `≈ 22–31`) is the **target for an
independent physics derivation of the inflation-epoch mode set** — it is
**NOT** a result produced here, and **NOT** evidence that `A_s` closes.
Selecting the mode set requires the Phase-1/Phase-2 mode-activation cascade
(36+252 hidden-mode structure, slow-roll ladder `ε_k = 1/[2(36−k)]`, pivot
`k=8`) — a physics judgment deliberately **not** delegated to this pipeline,
precisely because an agent optimizing for "`A_s` matches Planck" would fit
the mode set to the answer. This deliverable supplies only the mechanical,
verifiable machine and transfer function.

---

## Tier / audit summary

- **T1 (pure Mathlib axioms `propext, Classical.choice, Quot.sound`):**
  `cascadeVar_eq`, `cascadeVar_reproduces_kappa2_hid`,
  `kappa2_full_minus_modeGrounded`, `kappa2_modeGrounded_bracket`,
  `kappa2_visible_spread_bracket`, `AsValue_full_is_CC_scale`,
  `As_band_matching_kappa_inf` (verified by `#print axioms`).
- **T2 (existing cited axiom only):** `kappa2Partial_singleton`/`_empty`
  additionally touch the pre-existing `VisFermion.y` (PDG 2024) — no new
  axiom introduced.

## Success-criteria map

1. `lake build` succeeds; no new `sorry`/`axiom`; pre-existing
   SelfModelDeficit theorems unchanged — **met**.
2. `kappa2Partial` mode-resolved; anchor `univ ∈ (529.42,529.43)` —
   **STOP / honest negative**: not reconstructible from repo per-mode data;
   divergence proved exactly (`= 2.48`, the ungrounded `κ₂_vis` spread).
3. empty & singleton `= 0` — **met** (proved).
4. `AsValue` defined; full-cumulant CC-scale verified — **met**.
5. `results/as_transfer.md` table for both prefactors + band-matching
   `κ₂ᶦⁿᶠ` — **met**.
6. band-matching `κ₂ᶦⁿᶠ ≈ 22–31` flagged as a TARGET for independent
   derivation, not a result — **met** (above).
7. per-mode reconstruction cannot preserve 529.42 ⇒ STOP + report the
   divergence — **met** (this is the headline; the divergence is the finding).
