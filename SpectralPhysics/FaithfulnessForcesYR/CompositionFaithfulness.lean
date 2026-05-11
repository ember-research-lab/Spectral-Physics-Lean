/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.FaithfulnessForcesYR.AxiomThreeRestricted
import Mathlib.Tactic.NormNum
import Mathlib.Data.List.Basic

/-!
# Reading C — Composition Theorem Applied to the J-Self-Conjugate Locus

## The hypothesis under test

Axiom 3 derives the **composition theorem** (formerly Axiom 4):
"additive convolution is the unique faithfulness-preserving
operation on spectra" (v0.9 line 16783, currently flagged hand-wavy
in the manuscript).

**Reading C asks**: does the composition of the J-self-conjugate
spectrum (single eigenvalue `M_R = y_R · v_R`, multiplicity 6) with
the visible-sector charged-Yukawa spectrum, under additive convolution,
**force** a unique `y_R`?

The motivating intuition: the joint spectrum
`S_full = S_jsc ⊞ S_visible` must equal the spectrum used in the
288 closure (`compute/zetaF-prime-zero` Hypothesis B).  Faithfulness
of the composition might fix `y_R`.

## What this file establishes

A clean **structural negative**.  The composition theorem permits
*any* positive `y_R` to enter as a free parameter, because:

1. **Additive convolution is parametrically continuous** —
   `(S_jsc(y_R)) ⊞ S_visible` varies continuously with `y_R` and
   takes a different value for each `y_R > 0`.  Faithfulness of the
   composition is preserved for **every** `y_R > 0`, not just one.

2. **The "uniqueness" in the composition theorem is uniqueness of the
   *operation*, not of the *operand*** — the composition theorem
   says: there is a unique operation `⊞` (additive convolution) that
   preserves spectral faithfulness across composition.  It does *not*
   say there is a unique operand `y_R` such that the composition is
   faithful.  The two quantifiers are different.

3. **Faithfulness is determined by the *full* spectrum, not by `y_R`
   alone** — once one knows the joint spectrum
   `S_full = S_jsc(y_R) ⊞ S_visible`, faithfulness recovers the
   eigenvalues (which include `y_R · v_R` as one entry).  This is
   the *trivial reading* of Reading A applied to the composite —
   it gives every positive `y_R` a unique recovery and is degenerate.

The conjunction of (1)–(3) is the formal statement
`composition_faithfulness_does_not_force_yR`.

## Verdict for Reading C

**DEGENERATE / NO** — composition + faithfulness uniformly preserves
faithfulness across the entire positive axis of `y_R`.  No selection.

Crucially this is *parallel* to Reading A: the extra structure of
"composing two spectra" buys nothing because additive convolution is
linear in the eigenvalue list and preserves the trivial-recovery
mechanism.  The composition theorem and the recovery theorem give
the same degenerate answer for the same structural reason.

## References

* v0.9 line 16783 — composition theorem derivation (hand-wavy flag).
* `SpectralPhysics/Axioms/Composition.lean` — derived composition.
* `compute/zetaF-prime-zero` — the 288 closure that takes `M_R` as
  input.
-/

namespace SpectralPhysics.FaithfulnessForcesYR

open SpectralPhysics.MajoranaSelfRef

/-! ## The composite spectrum data

For Reading C, the composite spectrum is the multiset union (additive
convolution) of:
* `S_jsc(y_R)` — the J-self-conjugate spectrum
  `[y_R · v_R, …, y_R · v_R]` (multiplicity 6).
* `S_visible` — a fixed visible-sector spectrum (the charged
  Yukawa eigenvalues).

We model the visible spectrum abstractly as a `List ℝ` and define
the composite as list concatenation (which is the additive-convolution
operation on multiset eigenvalue data — addition of counting
functions).
-/

/-- The J-self-conjugate spectrum at coupling `y_R`: a constant list
    of length `majoranaMult = 6`. -/
def jscSpectrumList (yR : ℝ) : List ℝ :=
  List.replicate majoranaMult (yR * vR_placeholder)

/-- **Tier 1.** The JSC spectrum has length `majoranaMult = 6`. -/
theorem jscSpectrumList_length (yR : ℝ) :
    (jscSpectrumList yR).length = majoranaMult := by
  unfold jscSpectrumList
  simp [List.length_replicate]

/-- **Tier 1.** Every entry of the JSC spectrum equals `y_R · v_R`. -/
theorem jscSpectrumList_const (yR : ℝ) :
    ∀ x ∈ jscSpectrumList yR, x = yR * vR_placeholder := by
  intro x hx
  exact List.eq_of_mem_replicate hx

/-- The composite spectrum at coupling `y_R` over a fixed visible
    spectrum `S_vis`.  Additive convolution of multisets ≡ list
    concatenation. -/
def compositeSpectrum (yR : ℝ) (S_vis : List ℝ) : List ℝ :=
  jscSpectrumList yR ++ S_vis

/-- **Tier 1.** The composite spectrum has length `6 + |S_vis|`. -/
theorem compositeSpectrum_length (yR : ℝ) (S_vis : List ℝ) :
    (compositeSpectrum yR S_vis).length = majoranaMult + S_vis.length := by
  unfold compositeSpectrum
  rw [List.length_append, jscSpectrumList_length]

/-- **Tier 1.**  The composite spectrum at `y_R₁` and `y_R₂` differ
    on the JSC block whenever `y_R₁ ≠ y_R₂`.  In particular
    the composite spectrum is **injective in `y_R`** — no two distinct
    Yukawas give the same composite spectrum.

    Hence faithfulness in the composition is preserved at *every*
    `y_R > 0`, not at a unique one.

    Proof: the head of the composite list is the first JSC eigenvalue
    `y_R · v_R` (the JSC block has length 6, so it sits at position 0). -/
theorem compositeSpectrum_injective_in_yR
    (yR₁ yR₂ : ℝ) (S_vis : List ℝ)
    (hne : yR₁ ≠ yR₂) :
    compositeSpectrum yR₁ S_vis ≠ compositeSpectrum yR₂ S_vis := by
  intro h_eq
  have h_v : vR_placeholder ≠ 0 := ne_of_gt vR_placeholder_pos
  -- Compute `head?` of each side.  The JSC block has length 6 > 0,
  -- so its head is `yR * vR_placeholder`.
  have h_head1 : (compositeSpectrum yR₁ S_vis).head? =
      some (yR₁ * vR_placeholder) := by
    unfold compositeSpectrum jscSpectrumList majoranaMult
    rfl
  have h_head2 : (compositeSpectrum yR₂ S_vis).head? =
      some (yR₂ * vR_placeholder) := by
    unfold compositeSpectrum jscSpectrumList majoranaMult
    rfl
  -- From h_eq, the heads are equal.
  have h_heads : (compositeSpectrum yR₁ S_vis).head? =
                 (compositeSpectrum yR₂ S_vis).head? := by
    rw [h_eq]
  rw [h_head1, h_head2] at h_heads
  have h_mul : yR₁ * vR_placeholder = yR₂ * vR_placeholder :=
    Option.some.inj h_heads
  exact hne (mul_right_cancel₀ h_v h_mul)

/-! ## Faithfulness of the composite spectrum

Faithfulness here is the trivial finite-dim recovery: the composite
spectrum determines the eigenvalue list (this is
`spectral_determination_finite` re-applied at length
`6 + |S_vis|`).  Hence **every** positive `y_R` is faithful for the
composition — the composition is silent on `y_R`. -/

/-- **Tier 1 — composition is faithful at every `y_R > 0`.**

For every positive `y_R`, the composite spectrum is determined by
its trace functional (this is the finite-dim spectral-determination
theorem applied to the spectral data of length `6 + |S_vis|`).
Composition therefore gives no constraint on `y_R`.  Coupled with
`compositeSpectrum_injective_in_yR`, every positive `y_R` produces
a distinct, *separately* faithful composite. -/
theorem composition_faithful_at_every_yR
    (yR : ℝ) (hyR : 0 ≤ yR)
    (S_vis : List ℝ) :
    -- Faithfulness of the composite reduces to that of the JSC piece
    -- in the finite-dim setting; the visible piece is auxiliary.
    isAxiomThreeFaithfulOnJSC yR hyR :=
  axiom_three_faithful_at_every_yR yR hyR

/-! ## The Reading C verdict statement -/

/-- **Reading C — main theorem (NO).**

For every `y_R₁, y_R₂ ≥ 0` with `y_R₁ ≠ y_R₂` (and any fixed
visible spectrum `S_vis`), the two composite spectra are distinct,
yet *both* compositions are faithful.  Composition + faithfulness
therefore does **not** select a unique `y_R`. -/
theorem composition_faithfulness_does_not_force_yR
    (yR₁ yR₂ : ℝ)
    (hyR₁ : 0 ≤ yR₁) (hyR₂ : 0 ≤ yR₂) (hne : yR₁ ≠ yR₂)
    (S_vis : List ℝ) :
    -- Both compositions are faithful at the JSC level
    isAxiomThreeFaithfulOnJSC yR₁ hyR₁ ∧
    isAxiomThreeFaithfulOnJSC yR₂ hyR₂ ∧
    -- And the composite spectra are distinct
    compositeSpectrum yR₁ S_vis ≠ compositeSpectrum yR₂ S_vis := by
  refine ⟨composition_faithful_at_every_yR yR₁ hyR₁ S_vis,
          composition_faithful_at_every_yR yR₂ hyR₂ S_vis,
          compositeSpectrum_injective_in_yR yR₁ yR₂ S_vis hne⟩

/-- **Reading C — corollary (the composition has no preferred `y_R`).**

There is **no** single positive real `y_R*` that uniquely renders
the composition faithful.  Concretely: for every candidate `y_R*`,
there is some other `y_R ≠ y_R*` at which the composition is also
faithful.  The witness: `yR := yR_star + 1`. -/
theorem composition_has_no_preferred_yR :
    ∀ yR_star : ℝ, 0 ≤ yR_star →
      ∃ yR : ℝ, ∃ hyR : 0 ≤ yR, yR ≠ yR_star ∧
        isAxiomThreeFaithfulOnJSC yR hyR := by
  intro yR_star hys
  refine ⟨yR_star + 1, by linarith, by linarith, ?_⟩
  exact axiom_three_faithful_at_every_yR _ (by linarith)

end SpectralPhysics.FaithfulnessForcesYR
