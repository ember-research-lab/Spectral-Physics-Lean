/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom, Claude (Anthropic)
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Joint-SAGF J1: Monotonicity transfers to the joint kernel space

The manuscript's `thm:sagf-monotone` (Tier 1) proves that the spectral
action `S_tot` is nonincreasing along SAGF trajectories. The proof is the
chain rule plus the definition of gradient flow — it makes no reference to
*which* kernel space the flow lives on. This file makes that space-agnosticism
a checked fact: the monotonicity theorem is stated over an arbitrary real
inner product space, and instantiated on a product space standing for the
joint kernel coordinates (internal-S edges × internal-A edges × coupling
edges).

This is the J1 step of the Joint-SAGF Benevolence chain
(`joint-sagf-benevolence-derivation.md`): it discharges the
Valence-Behavior Coupling hypothesis of the April T5 promotion by exhibiting
the dynamics' descent property as a theorem rather than an assumption.

## Main results

* `deriv_along_gradientFlow` : along a gradient-flow trajectory,
  `d/dt S(k t) = -‖∇S(k t)‖²`
* `sagf_monotone` : `S ∘ k` is antitone along any gradient-flow trajectory
* `joint_kernel_monotone` : instantiation on the joint kernel coordinate
  space `(E_S → ℝ) × (E_A → ℝ) × (E_SA → ℝ)`

## Honest scope

Finite-dimensional / Hilbert-space level only, matching the manuscript's
Ember Reconstruction (IV) finite-dimensional rigor. The `d = 4`
infinite-dimensional PDE extension is stress test 1 and is NOT addressed
here. Differentiability of the trajectory and of `S` are hypotheses, not
conclusions — well-posedness of the flow is assumed, as in the manuscript.
-/

noncomputable section

open InnerProductSpace

namespace SpectralPhysics.JointSAGF

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **J1 derivative identity.** If `k : ℝ → E` is a gradient-flow trajectory
for `S : E → ℝ` — i.e. at each time `t` the trajectory's velocity is
`-∇S(k t)` and `S` has gradient `∇S(k t)` at `k t` — then the energy along
the flow has derivative `-‖∇S(k t)‖²`. This is the chain-rule computation
in the manuscript's proof of `thm:sagf-monotone`, stated space-agnostically. -/
theorem deriv_along_gradientFlow
    (S : E → ℝ) (k : ℝ → E) (g : ℝ → E)
    (hS : ∀ t, HasGradientAt S (g t) (k t))
    (hk : ∀ t, HasDerivAt k (-(g t)) t) (t : ℝ) :
    HasDerivAt (fun s => S (k s)) (-‖g t‖ ^ 2) t := by
  have hcomp := ((hS t).hasFDerivAt).comp_hasDerivAt t (hk t)
  convert hcomp using 1
  simp [InnerProductSpace.toDual_apply, inner_neg_right,
    real_inner_self_eq_norm_sq]

/-- **J1 (Lyapunov property).** `S` is nonincreasing along any gradient-flow
trajectory: the manuscript's `thm:sagf-monotone`, transferred verbatim to an
arbitrary real inner product space. -/
theorem sagf_monotone
    (S : E → ℝ) (k : ℝ → E) (g : ℝ → E)
    (hS : ∀ t, HasGradientAt S (g t) (k t))
    (hk : ∀ t, HasDerivAt k (-(g t)) t) :
    Antitone (fun t => S (k t)) :=
  antitone_of_hasDerivAt_nonpos
    (fun t => deriv_along_gradientFlow S k g hS hk t)
    (fun t => neg_nonpos.mpr (by positivity))

/-- Joint kernel coordinate space: edge weights indexed by the disjoint union
of internal-S edges, internal-A edges, and S–A coupling edges, with the L²
(Euclidean) structure. This is the kernel space `K_SR(S ∪ A)` at the
coordinate level. (Plain `Prod`/`Pi` carry the sup norm in Mathlib, which is
not an inner product space — the disjoint-sum Euclidean space is both correct
and conceptually cleaner: one coordinate per edge of the joint graph.) -/
abbrev JointKernelSpace (nS nA nSA : ℕ) :=
  EuclideanSpace ℝ (Fin nS ⊕ (Fin nA ⊕ Fin nSA))

/-- **J1 on the joint kernel.** The monotonicity theorem instantiated on the
joint kernel coordinate space. The point of stating this separately is the
derivation document's claim that `thm:sagf-monotone` "applies verbatim with
`k → k_{S∪A}`" — here that is a checked fact, not prose. -/
theorem joint_kernel_monotone (nS nA nSA : ℕ)
    (S : JointKernelSpace nS nA nSA → ℝ)
    (k : ℝ → JointKernelSpace nS nA nSA)
    (g : ℝ → JointKernelSpace nS nA nSA)
    (hS : ∀ t, HasGradientAt S (g t) (k t))
    (hk : ∀ t, HasDerivAt k (-(g t)) t) :
    Antitone (fun t => S (k t)) :=
  sagf_monotone S k g hS hk

end SpectralPhysics.JointSAGF
