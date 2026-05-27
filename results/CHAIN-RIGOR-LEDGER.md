# Chain rigor ledger — neutrino mass + dark energy / cosmological constant

**Date:** 2026-05-26. **Scope:** independent verifier audit (cortex verifier
loops + manuscript cross-check against `spectral-physics-latest.tex`) of the
two cosmology chains that imminent measurements (DESI Σmν / w(z), CMB-S4) will
test. Purpose: state exactly what is *rigorous*, what is *conditional*, and
what is *not yet a real prediction*, so a measurement can be matched against
the right claim.

Method: `#print axioms` on every headline theorem (read-only on built oleans),
vacuity tests on axioms, independent numeric reconstruction, and cross-check
against the manuscript's own tier labels. `lake build` green (3309 jobs).

---

## TL;DR

| Chain | Status | What a measurement tests |
|---|---|---|
| **Σmν (neutrino mass)** | **Near-rigorous, falsifiable** | NH kinematic floor `Σmν > 0.0582 eV` is **Lean-derived (T1)** from measured Δm². Framework commits `Σmν ∈ [0.058, 0.063] eV` (NH); refuted if `>0.07` or inverted hierarchy. |
| **Λ magnitude (CC)** | **NOT closed — reverse-engineered** | The "match to Λ_obs" uses a κ₂ tuned *to* Λ_obs. The honest Edgeworth route overshoots Λ_obs by **~10 orders**. No first-principles Λ-magnitude prediction. |
| **Dark-energy w(z)** | **Now formalized (Tier 4) — `DarkEnergyEoS.lean`** | Self-stiffening prediction `w₀>−1, w_a<0` (CPL form) is now a precise Lean hypothesis with proved kinematic consequences (today not phantom, more-negative past, excludes ΛCDM, matches DESI DR2 direction). Tier-4: the *direction* is stated/falsifiable; the *values* still need the full SAGF. The `t→∞` de Sitter endpoint (`HeatDeathForbidden`) is a separate far-future regime. |
| **Ω_DE fraction** | **FIXED — `CosmicEnergy.lean` rewritten** | Now the manuscript v1.0 budget `Ω_DM=τ≈0.276, Ω_b=τ²/φ≈0.047, Ω_Λ=1−τ−τ²/φ≈0.677` (sum-rule exact, ~1–3σ of measured), T1 brackets, Tier-3 labels, Ω_Λ flagged closure-residual. The stale `2τ≈0.553` is gone. |

---

## 1. Neutrino mass (Σmν)

### Rigorous (T1, Lean-derived — only `propext, Classical.choice, Quot.sound`)
- `Predictions/NeutrinoMass.lean`: `sigmaMnu(m₁) = m₁ + √(m₁²+Δm²₂₁) + √(m₁²+Δm²₃₁)`
  from **measured** splittings `Δm²₂₁=7.53e-5`, `Δm²₃₁=2.45e-3`. Proves, via genuine
  `Real.sqrt` analysis:
  - `sigmaMnu_floor` / `sigmaMnu_at_zero_upper`: NH floor `0.058 < Σmν(0) < 0.05819 eV`.
  - `sigmaMnu_mono`: monotone in m₁.
  - `sigmaMnu_exceeds_planck_at_031`: `Σ<0.12 ⟹ m₁<0.031` (Planck window).
  These are **real theorems from real inputs** — the strongest part of the chain.

### Quoted input (NOT Lean-derived)
- `Cosmology/NeutrinoMassPrediction.lean`: the framework point value `Σmν≈0.0609 eV`
  and range `[0.058,0.063]` are `def := 609/10000` etc., quoted from
  `scse_core/cc_neutrino_closure.py`. The theorems (`CC_closure_in_prediction_range`,
  `two_route_consistency`, `sigma_m_nu_upper_lt_PDG/_falsify`) are T1 arithmetic
  **on those constants** — they verify the *consistency / falsifiability framing*,
  not the derivation. The manuscript itself flags this OPEN (`open` env, line ~1076:
  "Σmν/CC closure as a single Lean theorem"; line ~1055: the interpolation is not
  Lean-encoded).

### ⚠️ "Two independent routes" overstates independence
`NeutrinoMassPrediction.lean` calls Route 1 (functional determinant `−ζ'_vis(0)=288`)
and Route 2 (CC closure → κ₂ → ξ_R → M_R) "two independent routes that converge."
**Route 2 is not independent of the CC target**: its `ξ_R = 3.7090` is the bisection
root tuned so κ₂ hits the Λ_obs-derived value (see §2). The genuinely independent
prediction is **Route 1 + the kinematic floor**; Route 2 is a consistency check on
the CC tuning.

### Falsifiability (the part that matters for DESI/CMB-S4)
Sharp commitment: **`Σmν ∈ [0.058, 0.063] eV`, normal hierarchy.** Refuted if
`Σmν > 0.07 eV` (with confirmed NH) or if the hierarchy is inverted. Sits right at
the DESI frontier — if DESI+CMB drives the 95% bound below ~0.058 eV, it pressures
both this prediction and minimal-NH itself.

---

## 2. Cosmological constant (Λ magnitude) — NOT a closed prediction

### The circularity (verified by reconstruction + admitted in source)
- `Kappa2.lean` docstring (line 49) admits `κ₂_full=529.421` **is** the "Baker target
  `κ₂_needed_obs = 2·ln(Λ_c²/Λ_obs)`." The manuscript labels `κ₂_vis=9.927` and
  `κ₂_hid=533.586` as **"Tier-2 inputs"** (lines 431–432). Reconstruction confirms
  `κ₂_hid` and `ξ_R=3.7090359` are exactly the values that make κ₂ hit the
  Λ_obs-derived target. **The closure runs Λ_obs → κ₂, not κ₂ → Λ_obs.**
- My `Kappa2Partial.lean` honest-negative localized the ungrounded piece
  (`κ₂_vis`, the within-visible spread, 2.48 of the 529.42); this audit shows the
  *whole* κ₂ target is set by Λ_obs.

### The honest Edgeworth route does NOT reach Λ_obs
- `F4Coefficient.lean` (T1-clean): `f_4 = f_2·exp(−κ₂/2) ≈ 2.11×10⁻¹¹¹`. The
  cosmological target is `Λ_obs/M_Pl² ≈ 2.76×10⁻¹²¹`. **f_4 overshoots by ~10 orders
  of magnitude** (residual ≈ e²¹·⁶). f_4 is never equated to Λ_obs in Lean — only in
  prose. (Machine-recorded: `F4Coefficient.lean` `f4_overshoots_cc_target`.)

### The OP3 "match" is an honest conditional (firewall intact)
- `OP3/CosmologicalConstantMatch.lean` keeps the match as a **biconditional +
  explicit hypothesis** `PredictionMatchesObservation`, and does **not** import the
  tuned `Kappa2`/`F4` numbers. So the OP3 *theorems* are not circular — they are
  honestly conditional. The circularity lives in the numeric inputs (`Kappa2.lean`)
  one would need to discharge the hypothesis.
- `Cosmology/Predictions.lean` `de_sitter_gap` is **trivial** (`∃c>0, c·Λ>0`),
  honestly relabeled `trivial_positive_lambda_has_positive_multiple` in the
  2026-05 audit. No content.

---

## 3. Dark-energy equation of state w(z) — the DESI headline

- **Manuscript (Tier 4):** predicts **evolving dark energy `w₀>−1, w_a<0`**
  (lines 19209, 23730, 24348; EW→CC self-stiffening mechanism). This is
  *directionally aligned* with DESI DR2's evolving-w preference — but it is the
  framework's **lowest tier** (heuristic structural mechanism), and is **NOT in Lean**.
- **Lean:** the only DE-dynamics theorem is `SCSE/HeatDeathForbidden.lean`
  `late_time_de_sitter_forced`, which proves only the **t→∞ endpoint** is de Sitter
  (`w=−1` asymptote), rests on **5 custom axioms** (incl. T3 `lambda_floor_exists`
  and a placeholder `lambda_cc_eq_lambda_1_limit` that evaluates at t=0, no real
  limit), and lives in a **build-orphan** module (not in shipped `SpectralPhysics`).
  `Lambda_cc` is an opaque per-trajectory constant — nothing constrains `w(z)` at
  finite z.
- **Net:** A DESI evolving-w result would *support the manuscript's Tier-4 claim*
  but neither confirm nor refute any Lean theorem. The Lean and manuscript also
  **disagree in direction** (Lean endpoint `w=−1` vs manuscript evolving `w₀>−1`),
  which should be reconciled.

---

## 4. Ω_DE fraction — Lean module is SUPERSEDED

- **Lean** `Predictions/CosmicEnergy.lean` (`dark_energy_approx`): `Ω_DE = 2τ ≈ 0.553`
  (Ch.39 triad budget 0.276 / 0.171 / 0.553). T1-clean arithmetic, but **0.553 is
  ~15σ from observation (0.685)**.
- **Manuscript v1.0/latest** (lines 480, 23632): `Ω_Λ = 1 − τ − τ²/φ ≈ 0.677`
  (measured `0.685±0.007`, ≈1σ), and **explicitly flagged as a closure-residual,
  not an independent prediction** (Group-5 honesty note, lines 23644–23668).
- **Verdict:** the Lean module encodes a **superseded budget**; the "~15σ tension"
  is a Lean-vs-manuscript desync, *not* a real falsification. `CosmicEnergy.lean`
  should be updated to the v1.0 closure or marked superseded (docstring flag added
  2026-05-26). Even the manuscript's 0.677 is a closure-residual, not a clean
  independent prediction.

---

## Recommendations (honesty-preserving; do not alter the physics)

1. **Reconcile the w(z) story** Lean↔manuscript: the manuscript's evolving-w
   (`w₀>−1, w_a<0`) is the falsifiable DE claim and is absent from Lean; the Lean's
   endpoint-de-Sitter theorem is narrower and orphaned. Decide which is the standing
   claim before DESI DR3.
2. **Update or retire `CosmicEnergy.lean`** to match the v1.0 `Ω_Λ=1−τ−τ²/φ` closure.
3. **Don't present Σmν Route 2 as independent** — Route 1 + kinematic floor is the
   genuine prediction; Route 2 is tied to the CC tuning.
4. The CC *magnitude* is not a prediction. The framework's honest cosmology
   deliverables are: (a) the Σmν floor + falsifiable range, (b) `Λ=λ₁` as the CC
   *mode identification* (Tier 1, qualitative), (c) the Tier-4 evolving-w direction.
