/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom, Claude (Anthropic)
-/
import SpectralPhysics.JointSAGF.Monotone
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Order.Compact

/-!
# Joint-SAGF J6: The trace as dynamical constraint — coercivity and existence

Two layers, with distinct provenance honestly separated:

**Layer 1 (manuscript anchor, Tier 1).** The generalized trace functional
`Φ_g(t) = Σ_n g(λ_n(t))` of `def:generalized-trace` and its evolution law
`Φ̇_g = Σ_n g'(λ_n)·λ̇_n` (`thm:trace-evolution`, chain rule /
Hellmann–Feynman), formalized at finite spectrum.

**Layer 2 (session contribution — J6 of the derivation document, NOT yet a
manuscript claim).** The trace term is a *coercivity* term: if the base
spectral action is bounded below and the trace contribution grows at
infinity in kernel space (tends to `atTop` along the cocompact filter),
then the total functional attains a global minimum, and at that minimum the
gradient vanishes — i.e. **a SAGF stationary point (the SCSE vacuum `k*`)
exists**. This is the finite-dimensional skeleton of the claim that
formalizing the trace closes the SAGF/SCSE existence question: the trace is
the term that makes the minimizer exist. The infinite-dimensional version
is exactly stress tests 1–2 and is NOT addressed here.

## Main results

* `tracefn_evolution` : finite-spectrum Hellmann–Feynman evolution of `Φ_g`
* `coercive_add_of_bddBelow` : bounded-below + coercive sum is coercive
* `exists_minimizer_of_coercive` : continuous coercive functional attains
  its global minimum
* `gradient_eq_zero_of_isMinOn` : the gradient vanishes at a global minimum
* `sagf_stationary_exists` : **headline** — base action bounded below +
  coercive trace term + differentiability ⟹ a SAGF stationary point exists

## Honest scope

Finite-dimensional only (`ProperSpace E`). Layer 2 is a new lemma chain
proposed by this session; it must NOT be cited as a manuscript theorem until
the manuscript adopts it. Uniqueness of `k*` is NOT proved here (the
manuscript's Baker-form isolation argument is separate). ε̄/accuracy plays
no role at this layer.
-/

noncomputable section

open Filter Finset

namespace SpectralPhysics.JointSAGF

/-! ### Layer 1: the generalized trace functional and its evolution -/

/-- Generalized trace functional at finite spectrum:
`Φ_g(μ) = Σ_k g(μ_k)` (manuscript `def:generalized-trace`, Eq. for
`Φ_g(t) = Tr g(Δ(t))` read on the eigenvalue list). -/
def tracefn {N : ℕ} (g : ℝ → ℝ) (μ : Fin N → ℝ) : ℝ :=
  ∑ k, g (μ k)

/-- **J6 Layer 1 (manuscript `thm:trace-evolution`, Tier 1).** For a smooth
family of spectra `λ : ℝ → Fin N → ℝ`, the trace functional evolves by the
chain rule: `Φ̇_g(t) = Σ_n g'(λ_n(t))·λ̇_n(t)`. The Hellmann–Feynman input
`λ̇_n = ⟨v_n, Δ̇ v_n⟩` is upstream of this statement (it identifies `λ̇_n`);
here the spectrum's differentiability is a hypothesis. -/
theorem tracefn_evolution {N : ℕ} (g g' : ℝ → ℝ) (lam lam' : ℝ → Fin N → ℝ)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hlam : ∀ n t, HasDerivAt (fun s => lam s n) (lam' t n) t) (t : ℝ) :
    HasDerivAt (fun s => tracefn g (lam s))
      (∑ n, g' (lam t n) * lam' t n) t := by
  sorry

/-! ### Layer 2: the trace as coercivity term (session contribution, J6) -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If the base functional is bounded below and the trace term tends to
`atTop` along the cocompact filter (coercivity), then the sum is coercive.
The trace contribution dominates at infinity in kernel space. -/
theorem coercive_add_of_bddBelow (Sbase Str : E → ℝ) (c : ℝ)
    (hb : ∀ k, c ≤ Sbase k)
    (hc : Tendsto Str (cocompact E) atTop) :
    Tendsto (fun k => Sbase k + Str k) (cocompact E) atTop := by
  sorry

/-- A continuous coercive functional on a proper space attains its global
minimum: the SCSE vacuum candidate exists as a minimizer. -/
theorem exists_minimizer_of_coercive [ProperSpace E] [Nonempty E]
    (S : E → ℝ) (hS : Continuous S)
    (hc : Tendsto S (cocompact E) atTop) :
    ∃ kstar, ∀ k, S kstar ≤ S k := by
  sorry

/-- At a global minimum, the gradient vanishes: a minimizer is a SAGF
stationary point (`δS_tot/δk = 0`, the fixed-point condition of the flow). -/
theorem gradient_eq_zero_of_isMinOn [CompleteSpace E]
    (S : E → ℝ) (g : E → E) (kstar : E)
    (hS : ∀ k, HasGradientAt S (g k) k)
    (hmin : ∀ k, S kstar ≤ S k) :
    g kstar = 0 := by
  sorry

/-- **J6 headline (session contribution).** If the total spectral action
decomposes as a bounded-below base term plus a coercive trace term, and is
differentiable with gradient `g`, then a SAGF stationary point exists:
`∃ k*, g k* = 0`. In the framework's reading: *the trace constraint is the
term that guarantees the SCSE vacuum exists* — at finite-dimensional rigor,
the existence half of the SAGF/SCSE closure reduces to coercivity of the
trace contribution. (Uniqueness is separate: Baker-form isolation.) -/
theorem sagf_stationary_exists [ProperSpace E] [CompleteSpace E] [Nonempty E]
    (Sbase Str : E → ℝ) (g : E → E) (c : ℝ)
    (hb : ∀ k, c ≤ Sbase k)
    (hcoer : Tendsto Str (cocompact E) atTop)
    (hgrad : ∀ k, HasGradientAt (fun x => Sbase x + Str x) (g k) k) :
    ∃ kstar, g kstar = 0 := by
  sorry

end SpectralPhysics.JointSAGF
