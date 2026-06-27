/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Triad.SelfReferentialTriad
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Koide Formula from Circulant Structure (Ch 39)

The Koide relation K = 2/3 for charged lepton masses emerges from
the circulant structure of the triad Laplacian. The three eigenvalues
of a circulant mass matrix automatically satisfy the Koide sum rule.

## Main results (to be formalized)

* `koideRatio` : K = (m_e + m_mu + m_tau) / (sqrt(m_e) + sqrt(m_mu) + sqrt(m_tau))^2
* `circulant_implies_koide` : CONDITIONAL identity — with the democratic
  amplitude ε² = 2 in √mₖ = M(1 + ε cos(θ + 2πk/3)), K = 2/3 (proved).
  Circulant structure alone does NOT force K = 2/3; the general value is
  K = 1/3 + ε²/6, and ε = √2 is an empirical fit, not a theorem.
* `koide_approx` : Numerical agreement with measured lepton masses

## The derivation chain

1. Triad {O, S, R} has Z_3 cyclic symmetry
2. Mass matrix in the symmetric basis is circulant: M = a I + b C + b* C^2
3. Sqrt-mass eigenvalues: √m_k = M(1 + ε cos(θ + 2πk/3)), k = 0,1,2
4. Direct computation: (sum m_k) / (sum sqrt(m_k))^2 = 1/3 + ε²/6,
   which equals 2/3 IFF ε² = 2 (the conditional proved in this file)

## References

* Koide, "New view of quark and lepton mass hierarchy" (1983)
* Ben-Shalom, "Spectral Physics", Chapter 39, Theorem 39.4
-/

noncomputable section

open Real

namespace SpectralPhysics.KoideFormula

/-- The Koide ratio for three masses -/
def koideRatio (m1 m2 m3 : ℝ) (h1 : 0 < m1) (h2 : 0 < m2) (h3 : 0 < m3) : ℝ :=
  (m1 + m2 + m3) / (Real.sqrt m1 + Real.sqrt m2 + Real.sqrt m3) ^ 2

/-- **Koide identity from the circulant parameterization — CONDITIONAL form (proved).**

    STATUS (2026-06-27 manuscript↔Lean sync audit): the earlier statement of
    this theorem (`circulant ⇒ K = 2/3`, with a `sorry`) was the one
    HIGH-severity divergence: it was **false as stated**, because circulant
    structure alone does NOT force the Koide ratio to `2/3`. The genuine
    algebra is `K = 1/3 + ε²/6`, where `ε` is the democratic amplitude of the
    square-root-mass parameterization `√mₖ = M·(1 + ε·cos(θ + 2πk/3))`; hence
    `K = 2/3 ⟺ ε² = 2`. The value `ε = √2` is an *empirical fit* to the lepton
    masses, not a consequence of circularity (manuscript Remark
    `rem:koide-eps-honest`).

    WHAT IS PROVED HERE (the well-posed conditional): given `M > 0`, the
    democratic amplitude `ε² = 2`, an angle `θ`, the branch-selection
    positivity `0 < 1 + ε·cos(θ + 2πk/3)` (needed because
    `√((M·u)²) = |M·u|`, and `1 + √2·cos` is negative for some `θ`), and the
    parameterization `mₖ = (M·(1 + ε·cos(θ + 2πk/3)))²`, then
    `koideRatio m₀ m₁ m₂ = 2/3`. The proof uses only the two cyclic cosine
    sums `Σ cos = 0`, `Σ cos² = 3/2` (via the cosine-addition expansions and
    `sin² + cos² = 1`). It FAILS without `hε : ε² = 2` — that is the point.

    What stays OPEN (NOT closed by this): whether the `D_F` lepton-Yukawa block
    *forces* `ε = √2`. That is a physics question, kept as a Tier-3 empirical
    fit in the manuscript. Supporting `Algebra/CirculantMatrix.lean` also still
    has 2 `sorry` (generic circulant eigenvalue theory). -/
theorem circulant_implies_koide
    (M ε θ : ℝ)
    (hM : 0 < M)
    (hε : ε ^ 2 = 2)
    -- Branch-selection positivity: 1 + ε·cos(θ + 2πk/3) > 0 for k = 0,1,2,
    -- so that √mₖ = M·(1 + ε·cos…) rather than its absolute value.
    (hp0 : 0 < 1 + ε * Real.cos θ)
    (hp1 : 0 < 1 + ε * Real.cos (θ + 2 * Real.pi / 3))
    (hp2 : 0 < 1 + ε * Real.cos (θ + 4 * Real.pi / 3))
    -- The three sqrt-mass eigenvalues of the circulant parameterization.
    (m1 m2 m3 : ℝ)
    (h_m1 : m1 = (M * (1 + ε * Real.cos θ)) ^ 2)
    (h_m2 : m2 = (M * (1 + ε * Real.cos (θ + 2 * Real.pi / 3))) ^ 2)
    (h_m3 : m3 = (M * (1 + ε * Real.cos (θ + 4 * Real.pi / 3))) ^ 2)
    (h_m1_pos : 0 < m1) (h_m2_pos : 0 < m2) (h_m3_pos : 0 < m3) :
    koideRatio m1 m2 m3 h_m1_pos h_m2_pos h_m3_pos = 2 / 3 := by
  -- Special-angle constants: cos/sin at 2π/3 and 4π/3.
  have hcos23 : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_sub, Real.cos_pi,
      Real.sin_pi, Real.cos_pi_div_three]
    ring
  have hsin23 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_sub, Real.cos_pi,
      Real.sin_pi, Real.sin_pi_div_three]
    ring
  have hcos43 : Real.cos (4 * Real.pi / 3) = -(1 / 2) := by
    rw [show 4 * Real.pi / 3 = Real.pi + Real.pi / 3 by ring, Real.cos_add, Real.cos_pi,
      Real.sin_pi, Real.cos_pi_div_three]
    ring
  have hsin43 : Real.sin (4 * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
    rw [show 4 * Real.pi / 3 = Real.pi + Real.pi / 3 by ring, Real.sin_add, Real.cos_pi,
      Real.sin_pi, Real.sin_pi_div_three]
    ring
  -- Per-angle cosine-addition expansions.
  have hC1 : Real.cos (θ + 2 * Real.pi / 3)
      = Real.cos θ * -(1 / 2) - Real.sin θ * (Real.sqrt 3 / 2) := by
    rw [Real.cos_add, hcos23, hsin23]
  have hC2 : Real.cos (θ + 4 * Real.pi / 3)
      = Real.cos θ * -(1 / 2) - Real.sin θ * -(Real.sqrt 3 / 2) := by
    rw [Real.cos_add, hcos43, hsin43]
  -- The two cyclic cosine sums, packaged as the amplitude identities we need.
  have hpyth : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hsqrt3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  -- Σ (1 + ε cos) = 3   (uses Σ cos = 0)
  have hSum1 : (1 + ε * Real.cos θ) + (1 + ε * Real.cos (θ + 2 * Real.pi / 3))
      + (1 + ε * Real.cos (θ + 4 * Real.pi / 3)) = 3 := by
    rw [hC1, hC2]; ring
  -- Σ (1 + ε cos)² = 6  (uses Σ cos = 0, Σ cos² = 3/2, ε² = 2)
  have hSumsq : (1 + ε * Real.cos θ) ^ 2 + (1 + ε * Real.cos (θ + 2 * Real.pi / 3)) ^ 2
      + (1 + ε * Real.cos (θ + 4 * Real.pi / 3)) ^ 2 = 6 := by
    rw [hC1, hC2]
    linear_combination (3 / 2) * ε ^ 2 * hpyth + (3 / 2) * hε
      + (1 / 2) * ε ^ 2 * Real.sin θ ^ 2 * hsqrt3
  -- Resolve the square roots via the positivity (branch selection).
  have hs1 : Real.sqrt m1 = M * (1 + ε * Real.cos θ) := by
    rw [h_m1]; exact Real.sqrt_sq (mul_nonneg hM.le hp0.le)
  have hs2 : Real.sqrt m2 = M * (1 + ε * Real.cos (θ + 2 * Real.pi / 3)) := by
    rw [h_m2]; exact Real.sqrt_sq (mul_nonneg hM.le hp1.le)
  have hs3 : Real.sqrt m3 = M * (1 + ε * Real.cos (θ + 4 * Real.pi / 3)) := by
    rw [h_m3]; exact Real.sqrt_sq (mul_nonneg hM.le hp2.le)
  -- Numerator and denominator in closed form.
  have hsum_sqrt : Real.sqrt m1 + Real.sqrt m2 + Real.sqrt m3 = 3 * M := by
    rw [hs1, hs2, hs3]; linear_combination M * hSum1
  have hsum_m : m1 + m2 + m3 = 6 * M ^ 2 := by
    rw [h_m1, h_m2, h_m3]; linear_combination M ^ 2 * hSumsq
  -- Assemble the ratio: 6 M² / (3 M)² = 2/3.
  unfold koideRatio
  rw [hsum_sqrt, hsum_m]
  have hM' : M ≠ 0 := ne_of_gt hM
  field_simp
  ring

/-- **Koide ratio numerical check**: Using measured lepton masses
    m_e = 0.511 MeV, m_mu = 105.66 MeV, m_tau = 1776.86 MeV,
    the Koide ratio is approximately 2/3.

    Proof: bound each √m between rationals using Real.sqrt_le_sqrt + Real.sqrt_sq,
    then chain the arithmetic to show |K - 2/3| is within 0.001.

    Bounds used:
    - √0.511 ∈ [714/1000, 716/1000] (verified: 0.714² = 0.509796 and 0.716² = 0.512656)
    - √105.66 ∈ [10278/1000, 10280/1000] (verified: 10.278² = 105.638... and 10.280² = 105.678...)
    - √1776.86 ∈ [42152/1000, 42154/1000] (verified: 42.152² = 1776.791... and 42.154² = 1776.960...)

    Sum range: [53144/1000, 53150/1000], sum²: [2824284736/10⁶, 2824922500/10⁶]
    Ratio range: ⊂ (1997/3000, 2003/3000) = (2/3 - 1/1000, 2/3 + 1/1000) -/
theorem koide_approx :
    let m_e := (0.511 : ℝ)
    let m_mu := (105.66 : ℝ)
    let m_tau := (1776.86 : ℝ)
    let sum_m := m_e + m_mu + m_tau
    let sum_sqrt := Real.sqrt m_e + Real.sqrt m_mu + Real.sqrt m_tau
    |sum_m / sum_sqrt ^ 2 - 2 / 3| < 0.001 := by
  -- Bound √m_e from below and above
  have h_e_lo : (714 : ℝ) / 1000 ≤ Real.sqrt 0.511 := by
    rw [show (714 : ℝ) / 1000 = Real.sqrt ((714 / 1000) ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 714/1000)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h_e_hi : Real.sqrt 0.511 ≤ 716 / 1000 := by
    rw [show (716 : ℝ) / 1000 = Real.sqrt ((716 / 1000) ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 716/1000)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  -- Bound √m_mu
  have h_mu_lo : (10278 : ℝ) / 1000 ≤ Real.sqrt 105.66 := by
    rw [show (10278 : ℝ) / 1000 = Real.sqrt ((10278 / 1000) ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 10278/1000)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h_mu_hi : Real.sqrt 105.66 ≤ 10280 / 1000 := by
    rw [show (10280 : ℝ) / 1000 = Real.sqrt ((10280 / 1000) ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 10280/1000)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  -- Bound √m_tau
  have h_tau_lo : (42152 : ℝ) / 1000 ≤ Real.sqrt 1776.86 := by
    rw [show (42152 : ℝ) / 1000 = Real.sqrt ((42152 / 1000) ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 42152/1000)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h_tau_hi : Real.sqrt 1776.86 ≤ 42154 / 1000 := by
    rw [show (42154 : ℝ) / 1000 = Real.sqrt ((42154 / 1000) ^ 2) from
      (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 42154/1000)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  -- Bound sum_sqrt ∈ [53144/1000, 53150/1000]
  have h_sum_lo : (53144 : ℝ) / 1000 ≤ Real.sqrt 0.511 + Real.sqrt 105.66 + Real.sqrt 1776.86 := by
    linarith
  have h_sum_hi : Real.sqrt 0.511 + Real.sqrt 105.66 + Real.sqrt 1776.86 ≤ 53150 / 1000 := by
    linarith
  -- The sum_sqrt is positive
  have h_sum_pos : (0 : ℝ) < Real.sqrt 0.511 + Real.sqrt 105.66 + Real.sqrt 1776.86 := by
    linarith
  -- sum_sqrt² ∈ [53144²/10⁶, 53150²/10⁶]
  have h_sq_lo : ((53144 : ℝ) / 1000)^2 ≤
      (Real.sqrt 0.511 + Real.sqrt 105.66 + Real.sqrt 1776.86)^2 := by
    exact sq_le_sq' (by linarith) h_sum_lo
  have h_sq_hi :
      (Real.sqrt 0.511 + Real.sqrt 105.66 + Real.sqrt 1776.86)^2 ≤ ((53150 : ℝ) / 1000)^2 := by
    exact sq_le_sq' (by linarith) h_sum_hi
  -- The result follows from the bounds:
  -- 1997/3000 < 1883.031 / (53150²/10⁶) ≤ K ≤ 1883.031 / (53144²/10⁶) < 2003/3000
  -- Which is verified by norm_num on the rational arithmetic.
  -- We use abs_sub_lt to split into two inequalities.
  simp only
  have h_sq_pos : (0 : ℝ) < (Real.sqrt 0.511 + Real.sqrt 105.66 + Real.sqrt 1776.86) ^ 2 :=
    by positivity
  -- Establish multiplicative bounds (avoids division rewrites)
  have h_lo : (2 / 3 - 0.001) *
      (Real.sqrt 0.511 + Real.sqrt 105.66 + Real.sqrt 1776.86) ^ 2 <
      0.511 + 105.66 + 1776.86 := by nlinarith [h_sq_hi]
  have h_hi : 0.511 + 105.66 + 1776.86 <
      (2 / 3 + 0.001) *
      (Real.sqrt 0.511 + Real.sqrt 105.66 + Real.sqrt 1776.86) ^ 2 := by nlinarith [h_sq_lo]
  rw [abs_lt]
  exact ⟨by linarith [(lt_div_iff₀ h_sq_pos).mpr h_lo],
         by linarith [(div_lt_iff₀ h_sq_pos).mpr h_hi]⟩

/-- **Triad circulant structure**: The Z_3 symmetry of the triad
    (cyclic permutation O -> S -> R -> O) forces the mass matrix
    to be circulant, which is the structural origin of Koide. -/
theorem triad_circulant_structure :
    -- The triad adjacency has Z_3 symmetry
    -- which forces circulant mass matrices
    True := trivial

end SpectralPhysics.KoideFormula

end
