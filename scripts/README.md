# Lean Cheating-Detection Tooling

Anti-cheating audit scripts for the spectral-physics-lean repo. Built 2026-05 after the adversarial audit found ~12 vacuous-marker axioms named after famous literature theorems.

## Usage

### Quick regex-based check (fast, ~1 second)

```bash
cd spectral-physics-lean
bash scripts/check_axioms.sh
```

Scans for the canonical cheating patterns:
- Pattern 1: `axiom foo : ∃ _, True` (vacuous existential)
- Pattern 2: `axiom foo : ∀ _, True` (vacuous universal)
- Pattern 3: `axiom foo : (n : ℕ) = n` (reflexive tautology)
- Pattern 4: `axiom Foo : Type` (vacuous type axiom)
- Pattern 5: `def MyPredicate := True` (predicate-shell laundering)
- Pattern 6: explicit `placeholder` markers in axiom docstrings
- Pattern 7: `is_kk_product : True`-style structure fields

Returns a list of files/lines + remediation suggestions.

### Definitive Lean-elaboration check (slower, ~minutes)

```bash
cd spectral-physics-lean
python3 scripts/check_axioms_lean.py
```

For each `axiom` declaration:
1. Generate a Lean test file: `example : <axiom-statement> := by trivial` etc.
2. Compile the test.
3. If ANY trivial proof compiles → axiom is vacuous, flag it.

With `--apply-fixes`, rewrites vacuous axioms as theorems with placeholder docstrings.

### CI integration

Add to your pre-commit hook or CI pipeline:

```bash
#!/bin/bash
# Pre-commit: fail if any new vacuous axioms were added
cd spectral-physics-lean
output=$(bash scripts/check_axioms.sh)
if echo "$output" | grep -E "axiom.*∃.*True|axiom.*∀.*True\s*$|axiom.*: \([0-9]+ : .*\) = [0-9]+|axiom .* : Type$" | grep -v "/.lake/"; then
    echo "ERROR: vacuous axioms detected. Please fix before commit."
    echo "$output"
    exit 1
fi
```

## What was caught (2026-05 audit)

The original audit found 12+ vacuous axioms:
- `kassel_kunneth_tor_decomposition : ∃ _ : ULift Unit, True` (Kassel 1986)
- `loday_quillen_tsygan_rationality : ∀ A : Type, True` (Loday-Quillen-Tsygan)
- `dim_Cl06_irrep_eq_eight : (8 : ℕ) = 8` (Lawson-Michelsohn)
- `bott_periodicity_dim_eq_256 : (256 : ℕ) = 2 ^ 8` (Atiyah-Bott-Shapiro)
- `spin2_two_polarizations_4D : (2 : ℕ) = 2` (Weinberg 1965)
- `framework_three_generations : numGen = 3` (Furey 2018)
- `ember_reconstruction_five_sectors : 3 + 2 = 5` (v0.9.1)
- `AkramiMajid_braided_HC_existence : Type`
- `ChernCharacterBraided : Type`
- `octonions_are_drinfeld_twist_existence` (Albuquerque-Majid 1999)
- `vassilevich2003_a2_formula : ∃ _ : A2Coefficient, True`
- `mellin_heat_kernel_finite_spectrum_log_sum : ∃ z, z = informationContent V`
- `zetaF_nuR_deriv_at_zero : ∃ ζ'₀, ζ'₀ = -2·mult·log y_R`

All have been remediated to `theorem` declarations with placeholder docstrings explaining the audit-trail correction.

Predicate-shell instances (8) remain but now have prominent audit-warning docstrings.

## Discipline going forward

See `/home/aaron/ember-research-lab/RIGOROUS_WORKFLOW.md` for the full discipline document. Key rule: **before declaring any `axiom`, run the vacuity test. If `by trivial`, `rfl`, `decide`, `⟨_, rfl⟩`, or `⟨default, trivial⟩` closes the goal, it must be a `theorem`, not an `axiom`.**

## Patterns not yet automated

- Misleading theorem names (theorem proves trivial statement, named/documented as deep result). See `Cosmology/Predictions/de_sitter_gap` case study.
- Circular conditional axiomatization (`axiom A`, `theorem B := A`, `axiom C := B`).
- Numerical axiomatization without empirical labeling.

These require human judgment; the regex/elaboration scripts catch only the syntactic patterns.
