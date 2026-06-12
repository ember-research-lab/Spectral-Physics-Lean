import SpectralPhysics.InflationAsClosure.FrameworkPrimitives
import Mathlib.Data.Fintype.Pi

/-! # Sheet-count factorization: 5³·2² = 500 as combinatorics of crossing classes

Decomposes the Berry "crossover axiom" (the conditional input (i) of the
`A_s` closure) into separately-attackable pieces, following the
selection-corank session derivation note (SHEETCOUNT-DERIVATION-2026-06-12):

* **(A) Trace democracy over sectors** — at `σ_tr = 0` the conformal mode's
  resonant coupling engages the sector-symmetric channel, equally over the
  `N_sectors = 5` channels, per generation;
* **(B) Generation factorization** — the crossing factorizes over the
  `N_gen = 3` generations (generation-blindness; template:
  `Algebra/RegisterForcing.lean` trace register-blindness);
* **(C) Polarization double cover** — each of the `N_pol = 2` TT
  polarizations crosses through its own ℤ₂ (Landau–Zener π-holonomy) sheet;
* **(D) Class-weight rule** — the physical history occupies one class, and
  the effective `λ_σ` shift is `+ln(card classes)` (the open
  engagement-rule analog; sibling of `open:cabibbo-discrete` gap (iii)).

**What is PROVED here (zero axioms):** the counting layer. The class space
implied by (A)+(B)+(C) is `SectorAssignment × PolSheet` with
`SectorAssignment = (Fin N_gen → Fin N_sectors)` — reading (d4)'s
"1-of-125" labels made explicit as *assignments of a sector channel to each
generation* — and its cardinality is 500. This upgrades the axiom's bare
exponential `5^3 · 2^2` to combinatorics of an explicit configuration space.

**What is NOT proved:** (A)–(D) themselves. They enter the assembly theorem
as hypotheses — (A)+(B)+(C) as a single `Equiv` (the factorization of the
class space), (D) as the log-cardinality rule. The assembly is wiring;
the analysis lives in the named hypotheses.
-/

namespace SpectralPhysics.InflationAsClosure

/-- Reading (d4)'s homotopy-class labels, explicit: each generation is
assigned the sector channel through which its content crosses `σ_tr = 0`. -/
abbrev SectorAssignment := Fin N_gen → Fin N_sectors

/-- Per-polarization ℤ₂ sheet of the TT eigenvector double cover. -/
abbrev PolSheet := Fin N_pol → Bool

/-- The axiom's exponential IS the assignment count: `N_sectors ^ N_gen`
counts maps from generations to sector channels. -/
theorem card_sectorAssignment :
    Fintype.card SectorAssignment = N_sectors ^ N_gen := by
  simp [SectorAssignment]

theorem card_sectorAssignment_eq_125 :
    Fintype.card SectorAssignment = 125 := by
  rw [card_sectorAssignment, N_sectors_count, N_gen_count]; norm_num

/-- The TT exponential IS the sheet count: `2 ^ N_pol` counts ℤ₂ choices
per polarization. -/
theorem card_polSheet : Fintype.card PolSheet = 2 ^ N_pol := by
  simp [PolSheet]

theorem card_polSheet_eq_4 : Fintype.card PolSheet = 4 := by
  rw [card_polSheet, N_pol_count]; norm_num

/-- **The 500 is a cardinality**: the full crossing-class space has exactly
`5³ · 2² = 500` elements. -/
theorem card_crossing_classes :
    Fintype.card (SectorAssignment × PolSheet) = 500 := by
  rw [Fintype.card_prod, card_sectorAssignment_eq_125, card_polSheet_eq_4]

/-- **Assembly (hypothesis-gated).** If the physical crossing-class space
`Classes` factorizes per (A)+(B)+(C) — i.e. is equivalent to
`SectorAssignment × PolSheet` — and the class-weight rule (D) holds —
the `λ_σ` log-shift equals `ln(card Classes)` — then the shift is exactly
`ln 500`.  The two hypotheses are the precise formal residues of the
crossover axiom; deriving them is the program (see derivation note). -/
theorem sheet_count_assembly
    {Classes : Type} [Fintype Classes]
    (h_factorizes : Classes ≃ (SectorAssignment × PolSheet))
    (Δ : ℝ)
    (h_weight_rule : Δ = Real.log (Fintype.card Classes)) :
    Δ = Real.log 500 := by
  rw [h_weight_rule, Fintype.card_congr h_factorizes, card_crossing_classes]
  norm_num

/-- Consistency with the existing Tier-1 arithmetic
(`five_cubed_two_squared_eq_500` in `FrameworkPrimitives`): the cardinality
route and the arithmetic route agree. -/
theorem card_route_eq_arithmetic_route :
    Fintype.card (SectorAssignment × PolSheet) =
      N_sectors ^ N_gen * 2 ^ N_pol := by
  rw [Fintype.card_prod, card_sectorAssignment, card_polSheet]

end SpectralPhysics.InflationAsClosure
