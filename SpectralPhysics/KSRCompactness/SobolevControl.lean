/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.KSRCompactness.KSRSpace

/-!
# Sobolev-type growth control on `𝒦_SR`

This file defines the **Sobolev-type growth predicate** that controls
the eigenvalue tail of a `KSR`: there exists a constant `C > 0` and a
power `s` such that

  `|λ_n(T)| ≤ C / (n+1)^s`   for all `n : ℕ`.

For `s > 1` this is the natural Schatten-1 (trace-class) decay
condition; for `s > 1/2` it would only give Hilbert–Schmidt
(Schatten-2).  Following Simon 2005 §3.3 and Reed–Simon Vol. IV §VI,
the trace-ideal compactness theorem requires `s > 1` (so the tail is
absolutely summable with a uniform tail bound).

The Sobolev language matches v0.9 line 11082(a): "Sobolev-type
compactness on the space of Hermitian kernels with controlled
eigenvalue growth."  At the operator level, the eigenvalue decay
`|λ_n| ≤ C/n^s` is the **dual** statement to Sobolev `H^s`
regularity of the kernel (Weyl's law: if `K` is `H^s`-regular on a
compact `n`-manifold, its singular values decay like `n^{-s/n}`).
We carry the decay rate as a real parameter without committing to
the manifold-dimension translation, which is open at v0.9 line
11079(a).

## Sites this enables

* `RellichKondrachov.lean` — the named axiom that bounded Sobolev-`s`
  classes are compact in trace norm, for `s > 1`.
* `KSRCompactnessThm.lean` — the headline conditional theorem.

## References

* Simon, B., *Trace Ideals* (AMS Math. Surveys 120, 2005), §3.3
  (`I_p`-class compactness criteria), §1.4 (trace-norm topology).
* Reed–Simon, *Methods of Modern Math. Phys.*, Vol. IV, §VI
  (Schatten ideals).
* v0.9 line 11082(a): the `𝒦_SR` Sobolev compactness expectation.
-/

noncomputable section

open Classical

namespace SpectralPhysics.KSRCompactness

/-! ## The Sobolev-`s` growth predicate

`SobolevGrowth T s` : there exists a constant `C > 0` such that
`|λ_n(T)| ≤ C / (n+1)^s` for all `n`.  We use `(n+1)^s` rather than
`n^s` to avoid the `n = 0` degeneracy. -/

/-- **Sobolev-`s` growth control on a `KSR`** (v0.9 line 11082(a)).

`SobolevGrowth T s` means: there is a constant `C > 0` such that
the eigenvalue absolute values satisfy `|λ_n| ≤ C / (n+1)^s`.

For `s > 1` this gives trace-class decay (Schatten-1); for
`s > 1/2`, Hilbert–Schmidt (Schatten-2).  Only `s > 1` is used
downstream for trace-ideal compactness. -/
def SobolevGrowth (T : KSR) (s : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, |T.lam n| ≤ C / ((n : ℝ) + 1) ^ s

/-! ## Monotonicity in the growth exponent

Larger `s` is a *stronger* decay condition: `SobolevGrowth T s'` with
`s' ≥ s` and uniform `(n+1) ≥ 1` implies `SobolevGrowth T s`. -/

/-- Sobolev growth is **monotone decreasing** in the exponent `s`:
faster decay (larger `s`) implies slower decay (smaller `s`). -/
theorem SobolevGrowth.mono_exponent
    {T : KSR} {s s' : ℝ} (h_le : s ≤ s') (h_growth : SobolevGrowth T s') :
    SobolevGrowth T s := by
  obtain ⟨C, hC_pos, hC⟩ := h_growth
  refine ⟨C, hC_pos, ?_⟩
  intro n
  have h_one_le : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  -- Since `(n+1) ≥ 1` and `s ≤ s'`, `(n+1)^s ≤ (n+1)^s'`.
  have h_pow_mono : ((n : ℝ) + 1) ^ s ≤ ((n : ℝ) + 1) ^ s' :=
    Real.rpow_le_rpow_of_exponent_le h_one_le h_le
  have h_pow_pos : 0 < ((n : ℝ) + 1) ^ s := by
    apply Real.rpow_pos_of_pos
    linarith
  have h_pow_pos' : 0 < ((n : ℝ) + 1) ^ s' := by
    apply Real.rpow_pos_of_pos
    linarith
  -- `C / (n+1)^s' ≤ C / (n+1)^s`
  have h_div_mono : C / ((n : ℝ) + 1) ^ s' ≤ C / ((n : ℝ) + 1) ^ s := by
    rw [div_le_div_iff₀ h_pow_pos' h_pow_pos]
    have h_mul : C * ((n : ℝ) + 1) ^ s ≤ C * ((n : ℝ) + 1) ^ s' :=
      mul_le_mul_of_nonneg_left h_pow_mono (le_of_lt hC_pos)
    linarith
  exact le_trans (hC n) h_div_mono

/-! ## Sobolev-growth implies trace-class for `s > 1`

Standard fact: `Σ 1/(n+1)^s` converges for `s > 1` (Riemann ζ-series).
Combining with the comparison `|λ_n| ≤ C/(n+1)^s` would give summability
of `|λ_n|`, hence trace-class.

In the eigenvalue-shadow setting we already *assumed* trace-class as
part of the `KSR` data, so this is a consistency lemma:
`SobolevGrowth T s` with `s > 1` is **consistent** with `T.trace_class`
in the sense that the comparison-test bound holds.

We record the comparison bound but do NOT re-derive `trace_class`. -/

/-- Auxiliary lemma: `1 ≤ (n+1)^s` whenever `s ≥ 0`. -/
private theorem one_le_pow_succ_of_nonneg {n : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    1 ≤ ((n : ℝ) + 1) ^ s := by
  have h_one_le : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  exact Real.one_le_rpow h_one_le hs

/-- For `s > 0`, Sobolev-`s` growth gives the **uniform bound**
`|λ_n| ≤ C` for all `n`. -/
theorem SobolevGrowth.uniform_bound
    {T : KSR} {s : ℝ} (hs : 0 ≤ s) (h_growth : SobolevGrowth T s) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, |T.lam n| ≤ C := by
  obtain ⟨C, hC_pos, hC⟩ := h_growth
  refine ⟨C, hC_pos, ?_⟩
  intro n
  have h_lower : 1 ≤ ((n : ℝ) + 1) ^ s := one_le_pow_succ_of_nonneg hs
  have h_div_le : C / ((n : ℝ) + 1) ^ s ≤ C := by
    have h_pow_pos : 0 < ((n : ℝ) + 1) ^ s := by linarith
    rw [div_le_iff₀ h_pow_pos]
    have h_C_le : C ≤ C * ((n : ℝ) + 1) ^ s :=
      le_mul_of_one_le_right (le_of_lt hC_pos) h_lower
    exact h_C_le
  exact le_trans (hC n) h_div_le

/-! ## The Sobolev sublevel set

For each fixed `s` and constant `C > 0`, we define the **Sobolev-class
sublevel set** `KSRSobolev s C`: the set of `T : KSR` whose eigenvalue
decay is controlled by `C / (n+1)^s` *with this specific constant `C`*.

Then `{T | SobolevGrowth T s} = ⋃_{C > 0} KSRSobolev s C`. -/

/-- The **`(s, C)`-Sobolev sublevel set** of `𝒦_SR`. -/
def KSRSobolev (s C : ℝ) : Set KSR :=
  { T | ∀ n : ℕ, |T.lam n| ≤ C / ((n : ℝ) + 1) ^ s }

/-- The full Sobolev-`s` class as the union over the rate constant `C`. -/
theorem sobolev_growth_eq_union (T : KSR) (s : ℝ) :
    SobolevGrowth T s ↔ ∃ C : ℝ, 0 < C ∧ T ∈ KSRSobolev s C := by
  rfl

/-! ## "Closed under trace-norm topology" — the qualitative claim

Real statement: for fixed `s, C > 0`, the set `KSRSobolev s C` is
closed under the trace-norm topology on `𝒦_SR`.

At the eigenvalue-shadow level, *pointwise* limits of sequences
satisfying `|λ_n^{(k)}| ≤ C/(n+1)^s` for each `n` again satisfy the
same bound — closedness under pointwise limit is immediate.  The
trace-norm topology is *finer* than pointwise convergence on each
coordinate (trace-norm convergence implies coordinate-wise convergence
via `|λ_n - μ_n| ≤ ‖T - S‖_1`).  We record this as a Prop and prove
the pointwise-limit direction without invoking trace-norm machinery
explicitly. -/

/-- **Pointwise closure** of the Sobolev sublevel set under
coordinate-wise limits.

If `T_k → T` coordinate-wise and each `T_k ∈ KSRSobolev s C`, then
`T ∈ KSRSobolev s C`. -/
theorem KSRSobolev_pointwise_closed
    {s C : ℝ}
    (Tseq : ℕ → KSR) (T : KSR)
    (h_each : ∀ k, Tseq k ∈ KSRSobolev s C)
    (h_pointwise : ∀ n : ℕ,
      Filter.Tendsto (fun k => (Tseq k).lam n) Filter.atTop (nhds (T.lam n))) :
    T ∈ KSRSobolev s C := by
  intro n
  -- Pass to the limit in `|λ_n^{(k)}| ≤ C/(n+1)^s`.
  have h_bd : ∀ k, |(Tseq k).lam n| ≤ C / ((n : ℝ) + 1) ^ s := fun k =>
    (h_each k) n
  have h_abs_tendsto :
      Filter.Tendsto (fun k => |(Tseq k).lam n|) Filter.atTop (nhds |T.lam n|) :=
    (h_pointwise n).abs
  exact le_of_tendsto h_abs_tendsto (Filter.Eventually.of_forall h_bd)

end SpectralPhysics.KSRCompactness

end
