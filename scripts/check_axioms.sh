#!/usr/bin/env bash
# check_axioms.sh — Adversarial vacuity audit for Lean axioms.
#
# Lists every `axiom` declaration in SpectralPhysics/, extracts its statement,
# and flags axioms whose statements are pattern-matched as POTENTIALLY VACUOUS
# (trivially provable in Lean without any axiom).
#
# This is a STATIC heuristic check; the full vacuity test would attempt
# elaboration with `by trivial`/`rfl`/etc. and report which compile.
# For that, see check_axioms_lean.py (Lean-elaboration-based, slower).
#
# Patterns flagged (heuristic regex):
#   * `: ∃ _, True`           — trivially true existential
#   * `: ∀ _, True`           — trivially true universal
#   * `: (n : ℕ) = n`         — reflexive tautology
#   * `: T = T` for any T     — reflexive tautology
#   * `: Type` (bare)         — vacuous type axiom (any inhabited Type works)
#   * `: Nonempty (PUnit → A)`— vacuous nonempty predicate
#   * `: Nonempty Unit`       — trivially inhabited
#   * `: True`                — literal True
#
# Usage: ./scripts/check_axioms.sh [path-to-SpectralPhysics-dir]
# Default: ./SpectralPhysics/

set -euo pipefail

DIR="${1:-./SpectralPhysics}"

if [ ! -d "$DIR" ]; then
  echo "Error: $DIR is not a directory. Run from spectral-physics-lean root."
  exit 1
fi

echo "=== Lean axiom vacuity audit ==="
echo "Scanning: $DIR"
echo

# Total axiom count
TOTAL=$(grep -r "^axiom " --include="*.lean" "$DIR" 2>/dev/null | wc -l)
echo "Total axiom declarations: $TOTAL"
echo

echo "=== Pattern 1: vacuous existentials (∃ _, True) ==="
grep -rn "^axiom.*∃.*True" --include="*.lean" "$DIR" 2>/dev/null | head -50 || echo "  (none found)"
echo

echo "=== Pattern 2: vacuous universals (∀ _, True) ==="
grep -rn "^axiom.*∀.*True\s*$" --include="*.lean" "$DIR" 2>/dev/null | head -20 || echo "  (none found)"
echo

echo "=== Pattern 3: reflexive tautologies (literal n = n) ==="
# Match axioms like `: (n : T) = n` where n is the same on both sides
grep -rnE "^axiom.*: \([0-9]+ : [^)]+\) = [0-9]+\s*$" --include="*.lean" "$DIR" 2>/dev/null | head -20 || echo "  (none found)"
echo

echo "=== Pattern 4: bare Type axioms (axiom Foo : Type) ==="
grep -rnE "^axiom [a-zA-Z_][a-zA-Z0-9_]* : Type\s*$" --include="*.lean" "$DIR" 2>/dev/null | head -20 || echo "  (none found)"
echo

echo "=== Pattern 5: vacuous predicates (Prop := True or := Nonempty Unit) ==="
grep -rnE "^def .* : Prop := True\s*$" --include="*.lean" "$DIR" 2>/dev/null | head -20 || echo "  (no Prop := True)"
grep -rnE "^def .* : Prop := Nonempty PUnit" --include="*.lean" "$DIR" 2>/dev/null | head -20 || true
grep -rnE "^def .* : Prop := Nonempty Unit" --include="*.lean" "$DIR" 2>/dev/null | head -20 || true
grep -rnE "^def .* := Nonempty \(PUnit" --include="*.lean" "$DIR" 2>/dev/null | head -20 || true
echo

echo "=== Pattern 6: axiom statements with explicit 'placeholder' markers ==="
grep -rn "placeholder shape\|marker type\|axiom name only\|placeholder existence" --include="*.lean" "$DIR" 2>/dev/null | head -30 || echo "  (none found)"
echo

echo "=== Pattern 7: 'theorem' bodies using placeholder hypothesis predicates ==="
# Predicates like is_kk_product : True inside structures
grep -rn "is_kk_product\s*:\s*True\|is_real\s*:\s*True" --include="*.lean" "$DIR" 2>/dev/null | head -20 || echo "  (none found)"
echo

echo "=== Summary ==="
echo "Manual review required for any matches above. Each flagged axiom should:"
echo "  (a) Convert to 'theorem' with trivial proof + placeholder docstring, OR"
echo "  (b) Replace with non-vacuous content capturing the cited literature, OR"
echo "  (c) Delete and refer to literature in a comment."
echo
echo "For a definitive vacuity check (elaboration-based), use check_axioms_lean.py."
