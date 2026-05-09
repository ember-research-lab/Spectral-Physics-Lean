/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum

/-!
# SO(10) 16-Spinor Decomposition under SU(3) × SU(2) × U(1)

The 16-dimensional spinor representation of Spin(10) decomposes under the
Standard Model gauge group as a single fermion generation:

  16 = (3, 2)_{1/6}     Q_L      ← left-handed quark doublet (6 states)
     ⊕ (3̄, 1)_{−2/3}   u_R^c    ← right-handed up-quark (3 states)
     ⊕ (3̄, 1)_{1/3}    d_R^c    ← right-handed down-quark (3 states)
     ⊕ (1, 2)_{−1/2}    L_L      ← left-handed lepton doublet (2 states)
     ⊕ (1, 1)_{1}       e_R^c    ← right-handed electron (1 state)
     ⊕ (1, 1)_{0}       ν_R     ← right-handed neutrino (1 state)
                                    ───────
                                  Total: 16 states

This is the standard SU(5) → SU(3) × SU(2) × U(1) decomposition lifted to
SO(10) via 16 = 10 ⊕ 5̄ ⊕ 1 (Slansky 1981, eq. 8.13).

## Tier classification

* **Tier 1**: All multiplicity counts and the SU(3)³ anomaly cancellation are
  proved in this file with `decide` or basic arithmetic.
* The rep-theoretic data itself (which SU(3)/SU(2) reps appear, what hypercharges)
  is *given as data* — it's the structural input from the SO(10) embedding.

## References

* Slansky, R. (1981). "Group theory for unified model building."
  Phys. Rep. 79, 1–128. (Table 28 for 16-spinor decomposition.)
* Manuscript v7, Theorem 3371 and its remark on rep-theoretic origin of 3/16.
-/

namespace SpectralPhysics.YukawaHierarchy

/-! ## SU(3) representation labels -/

/-- The SU(3) representations that appear in the 16-spinor of SO(10). -/
inductive SU3Rep
  | one        -- color singlet, dim 1
  | three      -- fundamental, dim 3
  | threeBar   -- antifundamental, dim 3
  deriving DecidableEq, Repr

namespace SU3Rep

/-- Dimension of an SU(3) rep. -/
def dim : SU3Rep → ℕ
  | one      => 1
  | three    => 3
  | threeBar => 3

/-- Dynkin index `T_2(R)` (in the convention `T_2(fund) = 1/2`).
    For our purposes only the value `2 · T_2` (= 0 or 1) is needed. -/
def doubleDynkin : SU3Rep → ℕ
  | one      => 0
  | three    => 1   -- 2 · (1/2) = 1
  | threeBar => 1

/-- The SU(3) cubic anomaly `A(R)`, normalized so `A(3) = 1`, `A(3̄) = -1`. -/
def cubicAnomaly : SU3Rep → ℤ
  | one      => 0
  | three    => 1
  | threeBar => -1

end SU3Rep

/-! ## SU(2) representation labels -/

/-- SU(2) reps appearing in the 16-spinor of SO(10). -/
inductive SU2Rep
  | trivial    -- dim 1
  | doublet    -- dim 2 (fundamental)
  deriving DecidableEq, Repr

namespace SU2Rep

def dim : SU2Rep → ℕ
  | trivial => 1
  | doublet => 2

end SU2Rep

/-! ## The 16-spinor decomposition -/

/-- One sub-rep of SO(10) 16-spinor, labelled by SM particle content. -/
structure SubRep where
  name      : String
  su3       : SU3Rep
  su2       : SU2Rep
  hypercharge : ℚ          -- Y in the convention Q = T_3 + Y
  count     : ℕ            -- multiplicity (always 1 in the SM 16)
  deriving Repr

namespace SubRep

/-- Number of fermion states in this sub-rep. -/
def states (s : SubRep) : ℕ := s.count * s.su3.dim * s.su2.dim

end SubRep

/-- The canonical decomposition of the SO(10) 16-spinor under
    SU(3) × SU(2) × U(1) (one Standard Model generation). -/
def decomposition : List SubRep := [
  { name := "Q_L",   su3 := .three,    su2 := .doublet, hypercharge := (1 : ℚ) / 6,    count := 1 },
  { name := "u_Rc",  su3 := .threeBar, su2 := .trivial, hypercharge := -(2 : ℚ) / 3,   count := 1 },
  { name := "d_Rc",  su3 := .threeBar, su2 := .trivial, hypercharge := (1 : ℚ) / 3,    count := 1 },
  { name := "L_L",   su3 := .one,      su2 := .doublet, hypercharge := -(1 : ℚ) / 2,   count := 1 },
  { name := "e_Rc",  su3 := .one,      su2 := .trivial, hypercharge := 1,              count := 1 },
  { name := "nu_R",  su3 := .one,      su2 := .trivial, hypercharge := 0,              count := 1 }
]

/-- Total number of states in the decomposition. -/
def totalStates : ℕ := (decomposition.map SubRep.states).sum

/-- Total number of color-triplet states. -/
def coloredStates : ℕ :=
  (decomposition.filter (fun s => s.su3 ≠ .one)).map SubRep.states |>.sum

/-- Total number of color-singlet (lepton-like) states. -/
def colorSingletStates : ℕ :=
  (decomposition.filter (fun s => s.su3 = .one)).map SubRep.states |>.sum

/-! ## Tier-1 theorems: structural identities (proved by `decide` or arithmetic) -/

/-- The 16-spinor really has 16 states. -/
@[simp] theorem totalStates_eq_sixteen : totalStates = 16 := by decide

/-- 12 of the 16 states are color-triplet (live in SU(3) fundamental or antifundamental). -/
@[simp] theorem coloredStates_eq_twelve : coloredStates = 12 := by decide

/-- 4 of the 16 states are color-singlet (lepton-like). -/
@[simp] theorem colorSingletStates_eq_four : colorSingletStates = 4 := by decide

/-- Colored + color-singlet partitions the 16-spinor. -/
theorem split_total : coloredStates + colorSingletStates = totalStates := by decide

/-! ## SU(3) cubic anomaly cancellation -/

/-- Per sub-rep contribution to the SU(3)³ anomaly: `A(R_color) · mult_iso · count`. -/
def anomalyContribution (s : SubRep) : ℤ :=
  s.su3.cubicAnomaly * (s.su2.dim : ℤ) * (s.count : ℤ)

/-- Total SU(3)³ anomaly summed over the 16-spinor. -/
def totalCubicAnomaly : ℤ := (decomposition.map anomalyContribution).sum

/-- **Tier 1 theorem.** The SM is anomaly-free in SU(3)³: the 16-spinor of SO(10)
    has zero cubic SU(3) anomaly. -/
@[simp] theorem cubic_anomaly_cancels : totalCubicAnomaly = 0 := by decide

/-! ## Dynkin-index sum in the 16-spinor -/

/-- `2 · T_2(SU(3) | 16) = Σ doubleDynkin(R_color) · dim(R_iso) · count`. -/
def doubleDynkinSum : ℕ :=
  (decomposition.map (fun s => s.su3.doubleDynkin * s.su2.dim * s.count)).sum

/-- **Tier 1 theorem.** `T_2(SU(3) | 16) = 2`. Equivalently, `2 · T_2 = 4`.
    This matches the textbook value (Slansky 1981, table 28). -/
@[simp] theorem dynkin_SU3_in_16 : doubleDynkinSum = 4 := by decide

/-! ## Yukawa multiplicities in the finite Dirac operator D_F

The finite spectral triple `(A_F, H_F, D_F)` of the Standard Model has
`H_F = 384` dimensions split as 96 visible (4 × 16-states + chirality + particle/anti)
+ 288 hidden. The eigenvalue `y_f` of D_F associated with each charged
fermion `f` appears with a definite multiplicity given by the count of
states in the SM particle content carrying mass `y_f`. -/

/-- Multiplicity of a charged-fermion Yukawa eigenvalue in D_F.

    For a SM charged fermion `f`, the multiplicity is

      `mult(y_f) = (color dim) × (chirality factor 2) × (particle/anti factor 2)`

    `= 12` for quarks (3 colors × 2 × 2), `= 4` for leptons (1 × 2 × 2). -/
def DFMultiplicity (s : SubRep) : ℕ :=
  s.su3.dim * 2 * 2

/-- For SM up/down quarks (Q_L, u_R^c, d_R^c) the D_F multiplicity is 12. -/
@[simp] theorem mult_quark_eq_twelve {s : SubRep} (h : s.su3 ≠ .one) :
    DFMultiplicity s = 12 := by
  simp only [DFMultiplicity]
  cases hsu3 : s.su3 with
  | one      => exact absurd hsu3 h
  | three    => rfl
  | threeBar => rfl

/-- For SM charged leptons (L_L, e_R^c) the D_F multiplicity is 4. -/
@[simp] theorem mult_lepton_eq_four {s : SubRep} (h : s.su3 = .one) :
    DFMultiplicity s = 4 := by
  simp only [DFMultiplicity]
  rw [h]; rfl

end SpectralPhysics.YukawaHierarchy
