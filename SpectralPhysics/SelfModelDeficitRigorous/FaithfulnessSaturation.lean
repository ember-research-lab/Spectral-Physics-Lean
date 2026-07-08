/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Predictions.KoideFormula
import SpectralPhysics.Predictions.CabibboAngle

/-!
# The Faithfulness-Saturation Lemma (WITNESSED form) — open problem A

This module formalizes the **Faithfulness-Saturation Lemma**, the deepest
lever of the saturation-forcing program (candidate C3, verdict
`ember-tasks/saturation-forcing/output/VERDICT-FINAL.md`).  The lemma says:
for a **self-modeled** self-referential channel, naturality forbids strict
slack between content and capacity, so content = capacity (saturation); and
on the `ℤ/3` circulant carrier this pins the democratic amplitude to
`ε² = 2` (hence Koide `K = 2/3`) and, transported to the inter-unit channel,
the Cabibbo leading value `λ₀ = τ/(1+τ)`.

## Status: **PARTIAL** — the REDUCTION is closed; O1 and O2 stay OPEN.

This is an honest partial, in the sense of the falsifier spec
(`ember-tasks/faithfulness-saturation-lemma/falsifier-spec.md`).

* **CLOSED here (sorry-free, kernel-only axioms):** the geometric *reduction*
  `saturation ⟺ ‖(1−P₃)v‖ = ‖P₃v‖ ⟺ ε² = 2 ⟺ K = 2/3`, and the Cabibbo
  transport `saturation ⟹ λ₀ = τ/(1+τ) ⟹ λ = (150−23√5)/440`.  This part is
  finite-dimensional linear algebra on the circulant carrier; the norms
  pinch is concrete (`breakingNormSq = (3/2)M²ε²`, `carrierNormSq = 3M²`).

* **O1 (capacity identification) — STATED, not derived.**  That the
  intra-multiplet channel's *content* is the ℤ/3-breaking norm `‖(1−P₃)v‖`
  and its *capacity* is the carrier norm `‖P₃v‖` is a reading (insert
  `located-gap (b)`, "asserted, not yet derived").  It travels as the two
  explicit hypotheses `content = breakingNorm ch`, `capacity = carrierNorm ch`
  of `saturation_reduction`.

* **O2 (no-dead-weight / naturality) — OPEN residue axiom, NOT discharged.**
  The `≥` direction (naturality forbids strict slack, `capacity ≤ content`)
  is the operator-algebraic content of `conj:func-det` Step 4
  (spectral-physics.tex L13184–13191, "dead weight … violating naturality"),
  whose rigorous proof is open (`open:self-model-deficit-proof`).  It enters
  as a **named citation-bearing axiom** `naturalityNoDeadWeight`, conditional
  on the self-modeled guard `IsSelfModeledChannel`.  We do **NOT** prove it.

## Guarding — the anti-`288` discipline

The headline `faithfulness_saturation_lemma` is **NOT** unconditional over
channels (`∀ ch, ε² = 2` is FALSE — quarks and the hidden triplet are not
saturated).  It carries the guard `IsSelfModeledChannel ch`, mirroring the
`IsPhysicalSpectrum V →` fix that retired the unsound
`∀ V, negZetaPrimeAtZero V = 288` (`SelfModelDeficitUnconditional/Verdict.lean`,
"SOUNDNESS FIX 2").

## Smuggling check (see also the in-file `#print axioms` note at the end)

* No axiom fixes `ε²`, `K`, `λ`, or a channel dimension to a numeral.  The
  number `ε² = 2` emerges from `le_antisymm` (O2 ≥ + coherence ≤) composed
  with the *proved* carrier geometry — exactly as `288` emerges from
  `le_antisymm` + a combinatorial dimension in the deficit precedent.
* `IsSelfModeledChannel` is an **undefined** predicate symbol (no intro
  rule), so `naturalityNoDeadWeight` cannot derive `False`: one cannot prove
  the guard for a non-saturated channel.  Consistency model (mirrors
  `PhysicalSpectrum`): interpret `IsSelfModeledChannel ch := carrierNorm ch ≤
  breakingNorm ch`; then the axiom is a tautology and the class is nonempty
  (`leptonChannel`, `ε = √2`, equal norms).
* `breakingNormSq` / `carrierNormSq` are **defined geometrically** (sums of
  squares of the carrier vector's components), and their closed forms are
  *theorems*, not definitions — no gerrymandered predicate trivializes the
  pinch.

## Non-injectivity location (load-bearing, per the spec)

On the circulant family the full spectral map `(M,ε,θ) ↔ masses` **is
injective** — `full_map_injective_in_amplitude` proves that `breakingNormSq`
determines `ε²` at fixed `M`.  Hence the non-injectivity that O2's dead-weight
argument invokes (a one-parameter family of coherent contents the complement
cannot distinguish) canNOT live in this full map; it lives in the
naturality-restricted complementary/self-model records, which is inside O2's
open scope.  We do not claim it here.

## References

* Ben-Shalom, *Spectral Physics*, `thm:saturation` (carrier bound, ≤),
  `conj:func-det` Step 4 (no-dead-weight, ≥), `thm:cabibbo` Step 2.
* `SelfModelDeficitRigorous/Theorem.lean` (the `≤`+`≥`⇒`=` witnessed pattern).
* `SelfModelDeficitUnconditional/PhysicalSpectrum.lean` (the guard pattern).
-/

noncomputable section

open Real

namespace SpectralPhysics.SelfModelDeficitRigorous.FaithfulnessSaturation

open SpectralPhysics.KoideFormula

/-! ### Special-angle cosines/sines of the `ℤ/3` triad -/

private lemma cos_2pi3 : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_sub, Real.cos_pi,
    Real.sin_pi, Real.cos_pi_div_three]; ring

private lemma sin_2pi3 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_sub, Real.cos_pi,
    Real.sin_pi, Real.sin_pi_div_three]; ring

private lemma cos_4pi3 : Real.cos (4 * Real.pi / 3) = -(1 / 2) := by
  rw [show 4 * Real.pi / 3 = Real.pi + Real.pi / 3 by ring, Real.cos_add, Real.cos_pi,
    Real.sin_pi, Real.cos_pi_div_three]; ring

private lemma sin_4pi3 : Real.sin (4 * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
  rw [show 4 * Real.pi / 3 = Real.pi + Real.pi / 3 by ring, Real.sin_add, Real.cos_pi,
    Real.sin_pi, Real.sin_pi_div_three]; ring

private lemma cosAdd23 (θ : ℝ) :
    Real.cos (θ + 2 * Real.pi / 3) = Real.cos θ * (-(1 / 2)) - Real.sin θ * (Real.sqrt 3 / 2) := by
  rw [Real.cos_add, cos_2pi3, sin_2pi3]

private lemma cosAdd43 (θ : ℝ) :
    Real.cos (θ + 4 * Real.pi / 3) = Real.cos θ * (-(1 / 2)) - Real.sin θ * (-(Real.sqrt 3 / 2)) := by
  rw [Real.cos_add, cos_4pi3, sin_4pi3]

/-! ### The circulant carrier channel

A `CirculantChannel` is the `ℤ/3` generation carrier of one self-referential
unit: a mean scale `M`, a democratic amplitude `ε`, and a phase `θ`, with the
branch-selection positivity `1 + ε·cos(θ + 2πk/3) > 0` (needed so the
√-masses are the values, not their absolute values). -/
structure CirculantChannel where
  /-- Mean √-mass scale. -/
  M : ℝ
  /-- Democratic (ℤ/3-breaking) amplitude. -/
  ε : ℝ
  /-- Triad phase. -/
  θ : ℝ
  hM : 0 < M
  hp0 : 0 < 1 + ε * Real.cos θ
  hp1 : 0 < 1 + ε * Real.cos (θ + 2 * Real.pi / 3)
  hp2 : 0 < 1 + ε * Real.cos (θ + 4 * Real.pi / 3)

/-- The three √-mass eigenvalues of the circulant carrier. -/
def sm0 (ch : CirculantChannel) : ℝ := ch.M * (1 + ch.ε * Real.cos ch.θ)
def sm1 (ch : CirculantChannel) : ℝ := ch.M * (1 + ch.ε * Real.cos (ch.θ + 2 * Real.pi / 3))
def sm2 (ch : CirculantChannel) : ℝ := ch.M * (1 + ch.ε * Real.cos (ch.θ + 4 * Real.pi / 3))

/-- The democratic mode amplitude `⟨v, (1,1,1)/√3⟩·(1,1,1)/√3` has each
coordinate equal to the mean of the √-masses. -/
def meanMass (ch : CirculantChannel) : ℝ := (sm0 ch + sm1 ch + sm2 ch) / 3

/-- `‖P₃ v‖²` — squared norm of the projection of the √-mass vector onto the
democratic mode `(1,1,1)` (three coordinates, each `= meanMass`). -/
def carrierNormSq (ch : CirculantChannel) : ℝ :=
  meanMass ch ^ 2 + meanMass ch ^ 2 + meanMass ch ^ 2

/-- `‖(1−P₃) v‖²` — squared norm of the ℤ/3-breaking
(generation-distinguishing) part `v − meanMass·(1,1,1)`. -/
def breakingNormSq (ch : CirculantChannel) : ℝ :=
  (sm0 ch - meanMass ch) ^ 2 + (sm1 ch - meanMass ch) ^ 2 + (sm2 ch - meanMass ch) ^ 2

/-- Carrier norm `‖P₃ v‖` (capacity, O1). -/
def carrierNorm (ch : CirculantChannel) : ℝ := Real.sqrt (carrierNormSq ch)

/-- Breaking norm `‖(1−P₃) v‖` (content, O1). -/
def breakingNorm (ch : CirculantChannel) : ℝ := Real.sqrt (breakingNormSq ch)

/-! ### Closed forms of the two norms (the REDUCTION core — proved) -/

/-- The democratic mode carries the mean scale: `meanMass = M`
(uses only `Σ cos = 0`). -/
theorem meanMass_eq (ch : CirculantChannel) : meanMass ch = ch.M := by
  unfold meanMass sm0 sm1 sm2
  rw [cosAdd23 ch.θ, cosAdd43 ch.θ]; ring

/-- `‖P₃ v‖² = 3 M²`. -/
theorem carrierNormSq_eq (ch : CirculantChannel) : carrierNormSq ch = 3 * ch.M ^ 2 := by
  unfold carrierNormSq; rw [meanMass_eq]; ring

/-- `‖(1−P₃) v‖² = (3/2) M² ε²`, `θ`-free (uses `Σ cos = 0`, `Σ cos² = 3/2`). -/
theorem breakingNormSq_eq (ch : CirculantChannel) :
    breakingNormSq ch = 3 / 2 * ch.M ^ 2 * ch.ε ^ 2 := by
  unfold breakingNormSq sm0 sm1 sm2
  rw [meanMass_eq, cosAdd23 ch.θ, cosAdd43 ch.θ]
  have hpyth : Real.sin ch.θ ^ 2 + Real.cos ch.θ ^ 2 = 1 := Real.sin_sq_add_cos_sq ch.θ
  have hsqrt3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  linear_combination (1 / 2 * ch.M ^ 2 * ch.ε ^ 2 * Real.sin ch.θ ^ 2) * hsqrt3
    + (3 / 2 * ch.M ^ 2 * ch.ε ^ 2) * hpyth

/-- The saturation ratio `content²/capacity² = ε²/2`, `θ,M`-free.  This is the
non-vacuity dial: `ε² = 2 ⟹ ratio 1` (saturated), otherwise `≠ 1`. -/
theorem breakingNormSq_eq_ratio (ch : CirculantChannel) :
    breakingNormSq ch = ch.ε ^ 2 / 2 * carrierNormSq ch := by
  rw [breakingNormSq_eq, carrierNormSq_eq]; ring

/-! ### The pinch (saturation ⟺ ε² = 2) — proved -/

/-- **The norms pinch (squared form).**  `‖(1−P₃)v‖² = ‖P₃v‖² ⟺ ε² = 2`,
`θ`- and `M`-free.  This is the finite-dimensional linear-algebra core. -/
theorem breakingNormSq_eq_carrierNormSq_iff (ch : CirculantChannel) :
    breakingNormSq ch = carrierNormSq ch ↔ ch.ε ^ 2 = 2 := by
  rw [breakingNormSq_eq, carrierNormSq_eq]
  have hM2 : (0 : ℝ) < ch.M ^ 2 := pow_pos ch.hM 2
  constructor
  · intro h
    have hfac : ch.M ^ 2 * (3 / 2 * ch.ε ^ 2 - 3) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact absurd h1 (ne_of_gt hM2)
    · linarith
  · intro h; rw [h]; ring

/-- **The norms pinch (norm form).**  `‖(1−P₃)v‖ = ‖P₃v‖ ⟺ ε² = 2`. -/
theorem breakingNorm_eq_carrierNorm_iff (ch : CirculantChannel) :
    breakingNorm ch = carrierNorm ch ↔ ch.ε ^ 2 = 2 := by
  have ha : (0 : ℝ) ≤ breakingNormSq ch := by unfold breakingNormSq; positivity
  have hb : (0 : ℝ) ≤ carrierNormSq ch := by unfold carrierNormSq; positivity
  constructor
  · intro h
    have hsq : breakingNormSq ch = carrierNormSq ch := by
      have h2 : breakingNorm ch ^ 2 = carrierNorm ch ^ 2 := by rw [h]
      rwa [breakingNorm, carrierNorm, Real.sq_sqrt ha, Real.sq_sqrt hb] at h2
    exact (breakingNormSq_eq_carrierNormSq_iff ch).mp hsq
  · intro h
    have hsq : breakingNormSq ch = carrierNormSq ch :=
      (breakingNormSq_eq_carrierNormSq_iff ch).mpr h
    unfold breakingNorm carrierNorm; rw [hsq]

/-! ### The full spectral map is injective — non-injectivity location -/

/-- **The circulant carrier map is injective in the amplitude.**  At fixed `M`,
`breakingNormSq` determines `ε²`.  Consequently the non-injectivity that O2's
dead-weight argument invokes is NOT in this full geometric map — it must be
located in the naturality-restricted complementary records (inside O2's scope,
not claimed here). -/
theorem full_map_injective_in_amplitude (ch1 ch2 : CirculantChannel)
    (hM : ch1.M = ch2.M)
    (h : breakingNormSq ch1 = breakingNormSq ch2) :
    ch1.ε ^ 2 = ch2.ε ^ 2 := by
  rw [breakingNormSq_eq ch1, breakingNormSq_eq ch2, hM] at h
  have hM2 : (0 : ℝ) < ch2.M ^ 2 := pow_pos ch2.hM 2
  have h2 : ch2.M ^ 2 * ch1.ε ^ 2 = ch2.M ^ 2 * ch2.ε ^ 2 := by linear_combination 2 / 3 * h
  exact mul_left_cancel₀ (ne_of_gt hM2) h2

/-! ### From saturation to the Koide value K = 2/3 -/

/-- The three masses `mₖ = (√mₖ)²` of the carrier. -/
def mass0 (ch : CirculantChannel) : ℝ := (ch.M * (1 + ch.ε * Real.cos ch.θ)) ^ 2
def mass1 (ch : CirculantChannel) : ℝ := (ch.M * (1 + ch.ε * Real.cos (ch.θ + 2 * Real.pi / 3))) ^ 2
def mass2 (ch : CirculantChannel) : ℝ := (ch.M * (1 + ch.ε * Real.cos (ch.θ + 4 * Real.pi / 3))) ^ 2

theorem mass0_pos (ch : CirculantChannel) : 0 < mass0 ch := pow_pos (mul_pos ch.hM ch.hp0) 2
theorem mass1_pos (ch : CirculantChannel) : 0 < mass1 ch := pow_pos (mul_pos ch.hM ch.hp1) 2
theorem mass2_pos (ch : CirculantChannel) : 0 < mass2 ch := pow_pos (mul_pos ch.hM ch.hp2) 2

/-- **Saturation ⟹ Koide `K = 2/3`** on the carrier, via the proved
`KoideFormula.circulant_implies_koide` (`ε² = 2 ⟹ K = 2/3`). -/
theorem koide_of_epsilonSq_two (ch : CirculantChannel) (hε : ch.ε ^ 2 = 2) :
    koideRatio (mass0 ch) (mass1 ch) (mass2 ch) (mass0_pos ch) (mass1_pos ch) (mass2_pos ch)
      = 2 / 3 :=
  circulant_implies_koide ch.M ch.ε ch.θ ch.hM hε ch.hp0 ch.hp1 ch.hp2
    (mass0 ch) (mass1 ch) (mass2 ch) rfl rfl rfl (mass0_pos ch) (mass1_pos ch) (mass2_pos ch)

/-! ### The REDUCTION (sorry-free GIVEN O1, O2 as explicit hypotheses)

Mirrors `SelfModelDeficitRigorous/Theorem.lean`: the two bounds are EXPLICIT
Prop hypotheses; nothing is discharged.  `content`/`capacity` are free reals
identified with the carrier norms only through the O1 hypotheses, so O1 is
exposed, not smuggled. -/

/-- **Faithfulness-Saturation, reduction form.**  Given
* O1: `content = ‖(1−P₃)v‖` and `capacity = ‖P₃v‖` (capacity identification),
* coherence (`thm:saturation`, ≤): `content ≤ capacity`,
* O2 (`conj:func-det` Step 4, ≥): `capacity ≤ content`,

then the carrier saturates: `‖(1−P₃)v‖ = ‖P₃v‖`, hence `ε² = 2`.  Uses NO
axioms (kernel only): O1 and O2 travel as hypotheses. -/
theorem saturation_reduction (ch : CirculantChannel) (content capacity : ℝ)
    (hO1_content : content = breakingNorm ch)
    (hO1_capacity : capacity = carrierNorm ch)
    (h_coherence : content ≤ capacity)
    (h_naturality : capacity ≤ content) :
    ch.ε ^ 2 = 2 := by
  have hsat : breakingNorm ch = carrierNorm ch := by
    have := le_antisymm h_coherence h_naturality
    rwa [hO1_content, hO1_capacity] at this
  exact (breakingNorm_eq_carrierNorm_iff ch).mp hsat

/-! ### The WITNESSED headline (guarded; O2 = named OPEN residue axiom)

The guard `IsSelfModeledChannel` is an undefined predicate symbol (no intro
rule), mirroring `IsPhysicalSpectrum`.  O2 (`naturalityNoDeadWeight`) is a
named citation-bearing axiom conditional on the guard — labelled OPEN and NOT
discharged. -/

/-- **The self-modeled guard.**  "`ch` is the carrier of a self-referential
channel with `R∘M = id`."  Undefined predicate symbol — no introduction rule
is (or may be) provided; it marks the honest formal residue of Axiom
`ax:self-ref`.  Mirrors `SelfModelDeficitUnconditional.PhysicalSpectrum`. -/
axiom IsSelfModeledChannel : CirculantChannel → Prop

/-- **O2 — no-dead-weight / naturality (OPEN residue axiom; NOT discharged).**

The `≥` direction of the pinch: for a self-modeled channel, naturality forbids
strict slack, so `capacity ≤ content`, i.e. `‖P₃v‖ ≤ ‖(1−P₃)v‖`.  This is the
operator-algebraic content of `conj:func-det` Step 4
(spectral-physics.tex L13184–13191, "excess … dead weight … violating
naturality"), rigorous proof open (`open:self-model-deficit-proof`).

* Conditional on the guard (cannot fire on a non-self-modeled channel).
* A **general inequality** — mentions no numeral (`ε²`, `K`, `λ`, dimension).
  The number `ε² = 2` is produced downstream by `le_antisymm` + the proved
  carrier geometry, never by this axiom.
* We do **NOT** prove it.  The `∀`-quantified Lean form of the parent
  no-dead-weight fact (`SelfModelDeficitUnconditional`) is known UNSOUND; this
  witnessed, guard-conditional form is the honest replacement. -/
axiom naturalityNoDeadWeight (ch : CirculantChannel) :
    IsSelfModeledChannel ch → carrierNorm ch ≤ breakingNorm ch

/-- **Faithfulness-Saturation Lemma (WITNESSED headline).**

For a **self-modeled** circulant channel, with the established coherence bound
(`thm:saturation`, ≤), the naturality no-dead-weight axiom (O2, ≥) forces
saturation, pinning `ε² = 2`.

Guarded, NOT unconditional over channels — `∀ ch, ε² = 2` is FALSE (quarks,
hidden triplet).  The guard is load-bearing: `naturalityNoDeadWeight` needs
`h_self_modeled`.  `#print axioms` = kernel + `IsSelfModeledChannel` +
`naturalityNoDeadWeight` only. -/
theorem faithfulness_saturation_lemma (ch : CirculantChannel)
    (h_self_modeled : IsSelfModeledChannel ch)
    (h_coherence : breakingNorm ch ≤ carrierNorm ch) :
    ch.ε ^ 2 = 2 :=
  (breakingNorm_eq_carrierNorm_iff ch).mp
    (le_antisymm h_coherence (naturalityNoDeadWeight ch h_self_modeled))

/-- **Faithfulness-Saturation ⟹ Koide (witnessed headline).**  A self-modeled
carrier has `K = 2/3`. -/
theorem faithfulness_saturation_koide (ch : CirculantChannel)
    (h_self_modeled : IsSelfModeledChannel ch)
    (h_coherence : breakingNorm ch ≤ carrierNorm ch) :
    koideRatio (mass0 ch) (mass1 ch) (mass2 ch) (mass0_pos ch) (mass1_pos ch) (mass2_pos ch)
      = 2 / 3 :=
  koide_of_epsilonSq_two ch (faithfulness_saturation_lemma ch h_self_modeled h_coherence)

/-! ### Cabibbo transport — the SAME pinch on the inter-unit channel

`thm:cabibbo` Step 2: content `= ε_total = λ/(1−λ)`, capacity `= τ`.  The same
`≥` (naturality) closes Step 2, forcing `λ₀ = τ/(1+τ)`; the discrete
correction `(8+τ)/8` (Steps 3–4, untouched) gives the closed form.  The
`ε_total`-as-content reading is the transfer-specific slice of O1 (STATED). -/

private lemma tau_pos : 0 < τ := by
  rw [tau_closed_form]
  have h5 : Real.sqrt 5 < 5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  linarith

/-- **Cabibbo Step 2 from saturation.**  If the accumulated inter-unit mixing
saturates the tolerance bound, `λ/(1−λ) = τ`, then `λ = τ/(1+τ) = cabibboLeading`
(`= (7−√5)/22`). -/
theorem cabibbo_leading_of_saturation (lam : ℝ) (hlam : lam < 1)
    (hsat : lam / (1 - lam) = τ) :
    lam = cabibboLeading := by
  have h1 : (1 - lam) ≠ 0 := by linarith
  rw [div_eq_iff h1] at hsat
  have hτ : (1 + τ) ≠ 0 := by have := tau_pos; linarith
  rw [cabibboLeading, eq_div_iff hτ]
  linear_combination hsat

/-- **Full Cabibbo value from saturation.**  Saturation + the discrete
correction give `λ·(8+τ)/8 = (150−23√5)/440 = 0.224023719…`, via the existing
`cabibbo_closed_form`.  Same lemma, one transfer-specific reading. -/
theorem cabibbo_full_of_saturation (lam : ℝ) (hlam : lam < 1)
    (hsat : lam / (1 - lam) = τ) :
    lam * discreteCorrection = (150 - 23 * Real.sqrt 5) / 440 := by
  rw [cabibbo_leading_of_saturation lam hlam hsat, ← cabibbo_factored]
  exact cabibbo_closed_form

/-! ### Non-vacuity: positive witness + negative control

A vacuous principle would output "ratio 1" everywhere.  It does not: the pinch
is a genuine `iff`, saturated exactly at `ε² = 2`. -/

/-- A channel at `θ = 0` with amplitude `a ∈ [0, 2)`; all three positivity
branches hold (`1 + a·cos ≥ 1 − a/2 > 0`). -/
def channelAtZero (a : ℝ) (ha : 0 ≤ a) (ha2 : a < 2) : CirculantChannel where
  M := 1
  ε := a
  θ := 0
  hM := one_pos
  hp0 := by rw [Real.cos_zero]; linarith
  hp1 := by rw [zero_add, cos_2pi3]; linarith
  hp2 := by rw [zero_add, cos_4pi3]; linarith

private lemma sqrt2_lt_two : Real.sqrt 2 < 2 := by
  have h : Real.sqrt 2 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h

/-- **Positive witness (self-modeled, saturated).**  The charged-lepton
carrier `ε = √2` (`ε² = 2`): the lemma correctly predicts saturation and
`K = 2/3`. -/
def leptonChannel : CirculantChannel := channelAtZero (Real.sqrt 2) (Real.sqrt_nonneg 2) sqrt2_lt_two

theorem leptonChannel_epsSq : leptonChannel.ε ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem leptonChannel_saturates :
    breakingNormSq leptonChannel = carrierNormSq leptonChannel :=
  (breakingNormSq_eq_carrierNormSq_iff leptonChannel).mpr leptonChannel_epsSq

theorem leptonChannel_koide :
    koideRatio (mass0 leptonChannel) (mass1 leptonChannel) (mass2 leptonChannel)
      (mass0_pos leptonChannel) (mass1_pos leptonChannel) (mass2_pos leptonChannel) = 2 / 3 :=
  koide_of_epsilonSq_two leptonChannel leptonChannel_epsSq

/-- **Negative control (non-self-modeled, NOT saturated).**  A quark-like
carrier `ε = 3/2` (`ε² = 9/4 ≠ 2`).  Its ratio is `9/8 ≠ 1`, and crucially
`IsSelfModeledChannel` is NOT provable for it (undefined predicate) — so the
lemma does NOT predict saturation here.  This is the vacuity firewall. -/
def quarkChannel : CirculantChannel := channelAtZero (3 / 2) (by norm_num) (by norm_num)

theorem quarkChannel_epsSq : quarkChannel.ε ^ 2 = 9 / 4 := by
  show (3 / 2 : ℝ) ^ 2 = 9 / 4; norm_num

theorem quarkChannel_not_saturated :
    breakingNormSq quarkChannel ≠ carrierNormSq quarkChannel := by
  rw [ne_eq, breakingNormSq_eq_carrierNormSq_iff quarkChannel, quarkChannel_epsSq]; norm_num

/-- The quark control's ratio is `9/8`, not `1`: content strictly exceeds
capacity — coherence itself already fails there (independent of the guard). -/
theorem quarkChannel_ratio :
    breakingNormSq quarkChannel = 9 / 8 * carrierNormSq quarkChannel := by
  rw [breakingNormSq_eq_ratio, quarkChannel_epsSq]; ring

/-! ### Non-vacuity note — the hidden triplet

The hidden triplet (ledger #11) has `ε_H = 2 − 2.16·10⁻⁶`, so its ratio is
`ε_H²/2 ≈ 2 ≠ 1` (double-wall, `breakingNormSq_eq_ratio` with `ε² ≈ 4`).  It is
not self-modeled (`conj:func-det` Step 1: the hidden sector IS the self-model
capacity), so — as with the quarks — the lemma must NOT and does NOT predict
saturation.  (We do not build it as a `CirculantChannel`: at `ε ≈ 2` the
positivity branch is at its wall, `min_k (1 + ε cos) → 0`, so strict
positivity fails — itself a witness that `ε = 2` is the boundary, not a
self-modeled interior point.)

### `#print axioms` transcript (recorded; re-checkable)

```
#print axioms saturation_reduction
  -- [propext, Classical.choice, Quot.sound]          (kernel only; O1,O2 = hyps)

#print axioms faithfulness_saturation_lemma
  -- [propext, Classical.choice, Quot.sound,
  --  IsSelfModeledChannel, naturalityNoDeadWeight]    (kernel + guard + O2)

#print axioms faithfulness_saturation_koide
  -- [propext, Classical.choice, Quot.sound,
  --  IsSelfModeledChannel, naturalityNoDeadWeight]

#print axioms cabibbo_full_of_saturation
  -- [propext, Classical.choice, Quot.sound]          (kernel only)
```

No axiom pins `ε²`, `K`, `λ`, or a dimension to a numeral.  No gerrymandered
predicate trivializes no-dead-weight.  O2 (`naturalityNoDeadWeight`) is the
only OPEN residue axiom; O1 travels as hypotheses. -/

end SpectralPhysics.SelfModelDeficitRigorous.FaithfulnessSaturation

end
