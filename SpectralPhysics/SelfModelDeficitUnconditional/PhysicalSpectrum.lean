import SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta

/-! # The physicality predicate for visible spectra

## Why this file exists (SOUNDNESS FIX 2, 2026-06-12)

The 2026-05-27 soundness fix restricted `BekensteinInformationBound` and
`NaturalityCoherence` from a free `c : ℝ` to `negZetaPrimeAtZero V` — but
left `V : VisibleSpectrum` universally quantified.  Since
`VisibleSpectrum` is *arbitrary* finite spectral data and
`negZetaPrimeAtZero_eq : negZetaPrimeAtZero V = informationContent V` is a
theorem with `informationContent` a concrete sum, `NaturalityCoherence`
alone still derived `False`: the single-mode spectrum with `y = 1` has
`informationContent = 0`, against the asserted `288 ≤ 0`.  (Machine-checked
falsifier 2026-06-12: `still_inconsistent : False` with axiom set
`[propext, Classical.choice, Quot.sound, NaturalityCoherence]`, no
`sorryAx`; recorded in `results/AXIOM-SOUNDNESS-SWEEP.md`.)

The physics never claimed the bounds for arbitrary spectra: the
manuscript's Steps 3–4 (completeness / sector-faithfulness, v0.9 §8458–8468)
apply to the spectrum *realized at the SCSE fixed point*.  This file names
that restriction.

## The predicate

`IsPhysicalSpectrum V` is an **undefined predicate symbol** — no
introduction rule is (or may be) provided in this development.  It marks
the hypothesis "V is the visible spectrum realized at the self-consistent
fixed point", whose formal characterization is exactly the open
operator-algebraic content of v0.9.2 deferred item C.1.

## Consistency of the resulting axiom set

The set `{IsPhysicalSpectrum, BekensteinInformationBound,
NaturalityCoherence}` (the latter two conditional on the former) is
satisfiable relative to the ambient theory: interpret
`IsPhysicalSpectrum V := (informationContent V = 288)`.  Under this
interpretation both conditional axioms are theorems (via
`negZetaPrimeAtZero_eq`), and the interpreting class is nonempty —
`witnessSpectrum` below has `informationContent = 288`.  No falsifying
instantiation exists because the counterexample spectra cannot be proven
physical.
-/

namespace SpectralPhysics.SelfModelDeficitUnconditional.PhysicalSpectrum

open SpectralPhysics.SelfModelDeficitRigorous.SpectralZeta

/-- "V is the visible spectrum realized at the SCSE fixed point."
Undefined predicate symbol; see module docstring.  The two capacity
axioms (`BekensteinInformationBound`, `NaturalityCoherence`) are
conditional on this predicate — that conditionality IS the honest
formal residue of the manuscript's Steps 3–4. -/
axiom IsPhysicalSpectrum : VisibleSpectrum → Prop

/-- Nonemptiness witness for the consistency model: the single-mode
spectrum with `y = e^{−288}` has information content exactly 288. -/
noncomputable def witnessSpectrum : VisibleSpectrum where
  numModes := 1
  mult := fun _ => 1
  yukawa := fun _ => Real.exp (-288)
  yukawa_pos := fun _ => Real.exp_pos _

theorem witnessSpectrum_content :
    informationContent witnessSpectrum = 288 := by
  simp [informationContent, witnessSpectrum, Real.log_exp]

end SpectralPhysics.SelfModelDeficitUnconditional.PhysicalSpectrum
