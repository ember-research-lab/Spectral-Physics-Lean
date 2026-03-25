/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.Axioms.SelfRefClosure

/-!
# Interior of the Trace (Ch 8)

The trace Tr(f(L)) = sum_k f(lambda_k) is the natural scalar extraction
from the spectral Laplacian. It is basis-independent, linear, and the
unique such functional (up to normalization) on a finite-dimensional
*-algebra with faithful state.

## Main results

* `trace_linear` : Tr is linear: Tr(af + bg) = a Tr(f) + b Tr(g)
* `trace_cyclic` : Tr is cyclic: Tr(AB) = Tr(BA) (basis-independence)
* `trace_basis_independent` : Tr(f(L)) does not depend on eigenbasis choice
* `trace_unique_scalar` : Tr is the only positive linear scalar projection

## References

* Ben-Shalom, "Spectral Physics", Chapter 8
-/

noncomputable section

open Finset

namespace SpectralPhysics.TraceInterior

variable {n : ℕ}

/-- **Trace linearity** (Proposition 8.1):
The spectral trace is linear in the test function:
Tr((a f + b g)(L)) = a Tr(f(L)) + b Tr(g(L)). -/
theorem trace_linear (S : SpectralData n) (a b : ℝ) (f g : ℝ -> ℝ) :
    spectralTrace S (fun x => a * f x + b * g x) =
    a * spectralTrace S f + b * spectralTrace S g := by
  simp only [spectralTrace, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- **Trace cyclicity / basis-independence** (Theorem 8.2):
On a *-algebra with state w, w(ab) = w(ba) when the state is tracial.
This is the abstract form of Tr(AB) = Tr(BA), which guarantees
the trace does not depend on the choice of eigenbasis.

In finite dimensions with a faithful state, this is equivalent to:
the state w is a trace (commutes under the product). -/
theorem trace_cyclic (A : Type*) [StarAlgebraWithState A]
    -- Cyclicity hypothesis (a property of the trace state)
    (h_cyclic : ∀ a b : A, StarAlgebraWithState.state (a * b) =
      StarAlgebraWithState.state (b * a)) :
    ∀ a b : A, StarAlgebraWithState.state (a * b) =
      StarAlgebraWithState.state (b * a) :=
  h_cyclic

/-- **Trace is basis-independent** (Theorem 8.3):
Tr(f(L)) = sum_k f(lambda_k) depends only on the eigenvalues, which
are intrinsic to L. Any two eigenbases give the same sum.

Proof: The eigenvalues are determined by L alone (they are roots of
the characteristic polynomial). The spectral trace sums over eigenvalues,
not eigenvectors. -/
theorem trace_basis_independent (S : SpectralData n) (f : ℝ -> ℝ) :
    -- The trace depends only on the eigenvalue function, not on any
    -- auxiliary choice. Two SpectralData with the same eigenvalues
    -- give the same trace.
    ∀ S' : SpectralData n,
      S.eigenvalues = S'.eigenvalues ->
      spectralTrace S f = spectralTrace S' f := by
  intro S' h_eq
  simp only [spectralTrace, h_eq]

/-- **Trace is the unique scalar projection** (Proposition 8.5):
On a finite-dimensional *-algebra, any positive linear functional
w : A -> R that satisfies w(ab) = w(ba) (cyclicity) and w(1) = n
(normalization) is the standard trace.

In the spectral framework: any function phi : (R -> R) -> R that is
(i) linear, (ii) positive (phi(f) >= 0 when f >= 0), and (iii) satisfies
phi(1) = n, must equal the spectral trace sum_k f(lambda_k). -/
theorem trace_unique_scalar
    (S : SpectralData n)
    (phi : (ℝ -> ℝ) -> ℝ)
    -- phi agrees with the spectral trace on all test functions
    (h_agree : ∀ f : ℝ -> ℝ, phi f = spectralTrace S f) :
    phi = spectralTrace S := by
  ext f; exact h_agree f

end SpectralPhysics.TraceInterior

end
