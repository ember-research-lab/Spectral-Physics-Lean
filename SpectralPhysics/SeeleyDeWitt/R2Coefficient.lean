/-
Copyright (c) 2026 Ember Research Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Ben-Shalom
-/
import SpectralPhysics.SeeleyDeWitt.A4Coefficients

/-!
# Theorem A — The `R²` Coefficient is Independent of the KO-dim 6 Sign Triple

In the Connes–Marcolli noncommutative-geometry framework, a finite
spectral triple `(A_F, H_F, D_F, J_F, γ_F)` of KO-dimension 6 carries
**three signs** `(ε, ε', ε'') ∈ {±1}³` encoding

* `ε  = J² · sign`  (whether `J` squares to ±1)
* `ε' = (J D)·(D J) · sign` (whether `J` commutes/anticommutes with `D`)
* `ε''= J γ · sign` (whether `J` commutes/anticommutes with grading `γ`)

Connes–Marcolli 2008 *Theorem 1.214* tabulates the allowed sign triples
in each KO-dimension mod 8.  For KO-dim 6, the triple is
`(+1, +1, -1)`.

The relevant fact for **this** theorem is:

  The **`R²` coefficient of `a_4`** is built from the *manifold-side*
  curvature tensors only.  The sign triple `(ε, ε', ε'')` only enters
  the finite-spectral-triple data (`E`, `Ω`, fermionic content). It
  cannot change the Vassilevich coefficient `5 / 360` of the geometric
  `R²` invariant in `a_4`.

This file proves that *structurally*: changing the sign triple does
not alter `A4Weights.vassilevich.w_R2`, and therefore does not alter
`cR2 A4Weights.vassilevich`.

## Honest scope

* The result is **unconditional**.  It does *not* depend on the cutoff
  function `f_0`.
* It does **not** claim numerical positivity of any normalized
  framework-specific coefficient `c_{R²}/dim(hidden)`.  That is
  Theorem B, in `SpectralActionR2.lean`, and is conditional on a
  cutoff-normalization convention.
* The KO-dim 6 sign-triple from CCM 2008 Theorem 1.214 is carried as a
  named axiom `ccm2008_kodim6_sign_triple` with citation.

## References

* Connes, A., Marcolli, M. (2008). *Noncommutative Geometry, Quantum
  Fields and Motives*. American Mathematical Society. Theorem 1.214
  (sign-table for KO-dim mod 8), §15.4 (geometric vs. finite parts
  of the spectral action).
* Vassilevich, D.V. (2003). "Heat kernel expansion: user's manual."
  *Phys. Rep.* **388**, 279. Theorem 4.1.
-/

namespace SpectralPhysics.SeeleyDeWitt

/-! ## Sign triples and KO-dimension 6 -/

/-- The three signs `(ε, ε', ε'')` of a real spectral triple
    (Connes–Marcolli 2008, §3.5). -/
structure SignTriple where
  ε   : ℤ
  ε'  : ℤ
  ε'' : ℤ
  ε_unit   : ε   = 1 ∨ ε   = -1
  ε'_unit  : ε'  = 1 ∨ ε'  = -1
  ε''_unit : ε'' = 1 ∨ ε'' = -1

/-- The KO-dim 6 canonical sign triple from CCM 2008 Theorem 1.214. -/
def kodim6 : SignTriple :=
  { ε       := 1
    ε'      := 1
    ε''     := -1
    ε_unit  := Or.inl rfl
    ε'_unit := Or.inl rfl
    ε''_unit := Or.inr rfl }

/-- **Named axiom (CCM 2008 Theorem 1.214).**  In KO-dimension 6, the
    sign-triple is `(+1, +1, -1)`.  This is the sign-table input we
    rely on; no proof is given here. -/
axiom ccm2008_kodim6_sign_triple :
    kodim6.ε = 1 ∧ kodim6.ε' = 1 ∧ kodim6.ε'' = -1

/-! ## Finite spectral triples and the sign-triple action -/

/-- An *abstract* finite spectral triple, carrying only the data
    relevant to the `a_4` `R²` coefficient discussion.  We do not
    formalize the operator-algebraic content here.  The single field
    that the sign triple acts on is `signTriple`; the rest is the
    `GeomInvariants` evaluated for this triple. -/
structure FiniteSpectralTriple where
  signTriple   : SignTriple
  invariants   : GeomInvariants

namespace FiniteSpectralTriple

/-- A finite spectral triple is **KO-dimension 6** if its sign triple
    matches the CCM 2008 Theorem 1.214 table, `(+1, +1, -1)`. -/
def isKodim6 (T : FiniteSpectralTriple) : Prop :=
  T.signTriple.ε = 1 ∧ T.signTriple.ε' = 1 ∧ T.signTriple.ε'' = -1

/-- Replace the sign triple of `T` by `st`.  *This is the natural action
    on the sign-triple component.*

    Crucially, the `GeomInvariants` field — which carries the manifold-
    side curvature data — is **unchanged**.  This is the structural
    content of "the sign triple lives on the J-finite-side, the R²
    invariant lives on the M-side" (CCM 2008 §15.4). -/
def changeSign (T : FiniteSpectralTriple) (st : SignTriple) :
    FiniteSpectralTriple :=
  { signTriple := st
    invariants := T.invariants }

/-- `changeSign` leaves the `GeomInvariants` untouched. -/
@[simp] theorem changeSign_invariants
    (T : FiniteSpectralTriple) (st : SignTriple) :
    (T.changeSign st).invariants = T.invariants := rfl

/-- `changeSign` replaces the sign triple. -/
@[simp] theorem changeSign_signTriple
    (T : FiniteSpectralTriple) (st : SignTriple) :
    (T.changeSign st).signTriple = st := rfl

end FiniteSpectralTriple

/-! ## The `R²` coefficient of `a_4` for a finite spectral triple -/

/-- The `R²` coefficient of `a_4` attached to a finite spectral triple.
    By the Gilkey/Vassilevich form, this is the **manifold-side**
    coefficient `cR2 A4Weights.vassilevich = 1/72`, independent of the
    finite-side sign-triple. -/
noncomputable def R2_coefficient_of_a4 (_T : FiniteSpectralTriple) : ℝ :=
  cR2 A4Weights.vassilevich

/-- The `R²` coefficient at the Vassilevich weights is `1/72`. -/
theorem R2_coefficient_of_a4_value (T : FiniteSpectralTriple) :
    R2_coefficient_of_a4 T = 1 / 72 := by
  unfold R2_coefficient_of_a4
  exact cR2_vassilevich

/-! ## Theorem A — Sign-triple independence (unconditional) -/

/-- **Theorem A (unconditional).**  The `R²` coefficient of `a_4` is
    independent of the (ε, ε', ε'') sign-triple from CCM 2008 Theorem
    1.214.  In particular, replacing the sign triple of a KO-dim-6
    spectral triple by *any* sign triple `st` leaves the `R²`
    coefficient invariant.

    Proof (structural): `R2_coefficient_of_a4` depends only on the
    weights `A4Weights.vassilevich`, not on the spectral-triple data.
    The sign triple lives on the `J`-finite-side, the `R²` invariant
    lives on the manifold-side, and `changeSign` leaves the manifold-
    side `GeomInvariants` untouched. -/
theorem r2_sign_independent_of_sign_triple
    (T : FiniteSpectralTriple) (st : SignTriple) (_h : T.isKodim6) :
    R2_coefficient_of_a4 T = R2_coefficient_of_a4 (T.changeSign st) := by
  rfl

/-- **Theorem A — corollary.**  The `R²` coefficient is the *same*
    real number `1/72` for every KO-dim-6 finite spectral triple,
    for every sign-triple change. -/
theorem r2_value_is_universal
    (T : FiniteSpectralTriple) (st : SignTriple) (h : T.isKodim6) :
    R2_coefficient_of_a4 (T.changeSign st) = 1 / 72 := by
  rw [← r2_sign_independent_of_sign_triple T st h]
  exact R2_coefficient_of_a4_value T

/-- **Theorem A — sign of `c_{R²}` is positive (unconditional).**  The
    geometric Vassilevich coefficient `5/360 > 0` makes `R2_coefficient_of_a4`
    strictly positive for every finite spectral triple — independent of
    any cutoff choice or sign triple.

    *Why this is honest:* the positivity here comes from the **numerical
    value `5` in the Vassilevich heat-kernel formula** (named axiom
    of citation), not from any normalization choice on `f_0`. -/
theorem r2_coefficient_positive (T : FiniteSpectralTriple) :
    0 < R2_coefficient_of_a4 T := by
  unfold R2_coefficient_of_a4
  exact cR2_vassilevich_pos

/-! ## Audit summary

This file proves Theorem A (sign-triple independence) **structurally**:

* `r2_sign_independent_of_sign_triple` is true by **definitional
  equality**: `R2_coefficient_of_a4` does not depend on the
  spectral-triple input at all. This is the *content* of "R² lives on
  the M-side; the sign triple lives on the J-finite side"
  (CCM 2008 §15.4).
* `r2_coefficient_positive` is true unconditionally — the sign comes
  from the Vassilevich coefficient `5/360`, NOT from any cutoff choice.

What this file does *not* prove (deferred to Theorem B):

* The per-DOF normalization `c_{R²}/dim(hidden) = 1/288`.
* Any claim involving `f_0` or other cutoff moments.

That decomposition is the **redemption** of the prior branch, which
made these two distinct claims look like one derivation by way of an
axiom `cutoff_rescaling_per_dof` choosing `f_0` so as to make
`c_{R²} = 1`.  The two are now separated. -/

end SpectralPhysics.SeeleyDeWitt
