import SpectralPhysics.KSRCompactness.KSRCompactnessThm

open SpectralPhysics.KSRCompactness

noncomputable section

/-- A one-parameter family of kernels: eigenvalue `c` at index 0, zero elsewhere. -/
def kOf (c : ℝ) : KSR where
  lam := fun n => if n = 0 then c else 0
  trace_class := by
    have : (fun n : ℕ => |if n = 0 then c else 0|) = fun n => if n = 0 then |c| else 0 := by
      funext n; split_ifs <;> simp
    rw [this]
    exact summable_of_ne_finset_zero (s := {0}) (fun n hn => by simp at hn; simp [hn])
  srInvariant := True

theorem kOf_injective : Function.Injective kOf := by
  intro a b h
  have := congrArg (fun T : KSR => T.lam 0) h
  simpa [kOf] using this

theorem kOf_mem (s C : ℝ) (hC : 0 < C) (c : ℝ) (hc : |c| ≤ C) :
    kOf c ∈ KSRSobolev s C := by
  intro n
  simp only [kOf]
  split_ifs with h
  · subst h; simp; exact hc
  · simp; positivity

theorem ksr_false : False := by
  have hcpt := rellich_kondrachov_trace_class 2 1 (by norm_num) (by norm_num)
  haveI : DiscreteTopology KSR := ⟨rfl⟩
  have hfin : (KSRSobolev 2 1).Finite := hcpt.finite_of_discrete
  have hsub : kOf '' Set.Icc (0:ℝ) 1 ⊆ KSRSobolev 2 1 := by
    rintro _ ⟨c, ⟨h0, h1⟩, rfl⟩
    exact kOf_mem 2 1 (by norm_num) c (by rw [abs_of_nonneg h0]; exact h1)
  have himg : (kOf '' Set.Icc (0:ℝ) 1).Finite := hfin.subset hsub
  have hIcc : (Set.Icc (0:ℝ) 1).Finite := (himg.of_finite_image kOf_injective.injOn)
  exact (Set.Icc_infinite (by norm_num : (0:ℝ) < 1)) hIcc

#print axioms ksr_false
