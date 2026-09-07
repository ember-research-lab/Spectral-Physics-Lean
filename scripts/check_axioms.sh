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
#   * Pattern 8 (UNSOUNDNESS): an axiom with a numeric parameter (ℝ/ℕ/ℤ/ℚ) that
#       appears in an (in)equality — e.g. `axiom f (c : ℝ) : c ≤ X`. If `c` is
#       FREELY bounded (not constrained by a hypothesis), the axiom is FALSE at
#       some value (c = X+1) and is INCONSISTENT. This class is invisible to the
#       vacuity patterns 1–7 and was the 2026-05 bug (BekensteinInformationBound,
#       NaturalityCoherence, cheeger_lower/upper). Definitive test: derive
#       `example : False` from the axiom in a scratch file (see AXIOM-SOUNDNESS-SWEEP.md).
#   * Pattern 9: free STRUCTURE variable in an (in)equality with no Prop-hyp
#       binder. Added 2026-06-12 after sweep item 0b.
#   * Pattern 10 (2026-09-06): (a) `axiom` declaring an opaque Prop-valued
#       predicate symbol (type ends in `→ Prop` or `: Prop`); (b) any axiom
#       whose only hypotheses are such opaque predicates; plus Pattern 9's
#       gap — a structure-typed binder in an (in)equality guarded ONLY by an
#       `(h… : <opaque axiom predicate>)` binder (or an implication from one).
#       Historical SMDU forms: `IsPhysicalSpectrum`, `BekensteinInformationBound`,
#       `NaturalityCoherence`. Re-test: pipe `git show main:…` copies into a
#       temp dir and pass that dir as $1.
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

echo "=== Pattern 8: UNSOUNDNESS — false-universal bound/equality axioms ==="
echo "  Flags axioms with a numeric parameter (ℝ/ℕ/ℤ/ℚ) used in an (in)equality."
echo "  REVIEW each: is the parameter CONSTRAINED by a hypothesis (sound), or FREELY"
echo "  bounded (e.g. 'axiom f (c : ℝ) : c ≤ X') — which is FALSE at c=X+1 ⇒ UNSOUND?"
echo "  Definitive test: try to build 'example : False' from the axiom in a scratch file."
AX_FILES=$(find "$DIR" -name "*.lean")
if [ -n "$AX_FILES" ]; then
  awk '
    function flush() {
      if (inax && buf ~ /\([^():]*:[ ]*(ℝ|ℕ|ℤ|ℚ)[ ]*\)/ && buf ~ /≤|≥| < | > | = /) {
        gsub(/[ \t]+/, " ", buf); print "  " loc "  " buf
      }
      inax=0; buf=""
    }
    /^axiom / { flush(); inax=1; buf=$0; loc=FILENAME ":" FNR; next }
    inax && ($0 == "" || $0 ~ /^(def |theorem |lemma |namespace |end |open |\/-|--|@\[|instance |structure |inductive |abbrev )/) { flush(); next }
    inax { buf = buf " " $0 }
    END { flush() }
  ' $AX_FILES 2>/dev/null | head -60
else
  echo "  (no .lean files)"
fi
echo

echo "=== Pattern 9: UNSOUNDNESS — free STRUCTURE variable in bound/equality axioms ==="
echo "  (Added 2026-06-12 after sweep item 0b: a free structure-typed binder whose"
echo "  fields feed a computable definition is the SAME class as a free numeric"
echo "  variable — e.g. 'axiom f (V : VisibleSpectrum) : g V ≤ X' with computable g"
echo "  is FALSE at a counterexample V. Pattern 8 cannot see it.)"
echo "  Flags axioms with a non-numeric structure-typed binder in an (in)equality"
echo "  conclusion and NO Prop-hypothesis binder guarding it. REVIEW each: is every"
echo "  structure binder constrained by a hypothesis, or freely quantified?"
if [ -n "$AX_FILES" ]; then
  awk '
    function flush() {
      if (inax && buf ~ /\([A-Za-z_][A-Za-z0-9_]* :[ ]*[A-Z][A-Za-z0-9_.]*\)/ \
          && buf ~ /≤|≥| < | > | = / \
          && buf !~ /\(h[A-Za-z0-9_]* :/) {
        gsub(/[ \t]+/, " ", buf); print "  " loc "  " buf
      }
      inax=0; buf=""
    }
    /^axiom / { flush(); inax=1; buf=$0; loc=FILENAME ":" FNR; next }
    inax && ($0 == "" || $0 ~ /^(def |theorem |lemma |namespace |end |open |\/-|--|@\[|instance |structure |inductive |abbrev )/) { flush(); next }
    inax { buf = buf " " $0 }
    END { flush() }
  ' $AX_FILES 2>/dev/null | head -60
else
  echo "  (no .lean files)"
fi
echo

echo "=== Pattern 10: opaque Prop-predicate symbols + axioms they uniquely guard ==="
echo "  (Added 2026-09-06 after SMDU IsPhysicalSpectrum shells.)"
echo "  10a: axiom whose type is \`Prop\` or ends in \`→ Prop\` / \`-> Prop\`"
echo "       (undefined predicate *symbol*, not a stated proposition)."
echo "  10b: axiom whose only Prop-hypotheses are applications of 10a names"
echo "       (binders \`(h : Pred …)\` or implication antecedents \`Pred … →\`)."
echo "  9-gap: 10b with a structure-typed binder and an (in)equality conclusion"
echo "       — Pattern 9 misses this because the \`(h… : …)\` binder exists."
echo "  REVIEW each: a 10a symbol with no intro rule plus a 10b/9-gap axiom is"
echo "  a hypothesis=conclusion shell under the model Pred x := (conclusion)."
python3 - "$DIR" <<'PY'
import os, re, sys

dirpath = sys.argv[1]
STOP = re.compile(
    r"^(def |theorem |lemma |namespace |end |open |/-|--|@\[|instance |"
    r"structure |inductive |abbrev |axiom )"
)
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
INEQ = re.compile(r"≤|≥|<|>|=")
STRUCT_BINDER = re.compile(
    r"\(([A-Za-z_][A-Za-z0-9_]*)\s*:\s*([A-Z][A-Za-z0-9_.]*)\)"
)

def iter_lean_files(root):
    for dp, dns, fns in os.walk(root):
        dns[:] = [d for d in dns if d not in {".lake", ".git"}]
        for fn in fns:
            if fn.endswith(".lean"):
                yield os.path.join(dp, fn)

def collect_axioms(path):
    with open(path, encoding="utf-8", errors="replace") as f:
        lines = f.read().splitlines()
    out = []
    i = 0
    while i < len(lines):
        if lines[i].startswith("axiom "):
            start = i + 1
            buf = [lines[i]]
            i += 1
            while i < len(lines):
                s = lines[i]
                if s == "" or STOP.match(s):
                    break
                buf.append(s)
                i += 1
            text = re.sub(r"\s+", " ", " ".join(buf)).strip()
            out.append((path, start, text))
            continue
        i += 1
    return out

def split_colon(after_name):
    depth = 0
    for i, ch in enumerate(after_name):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch == ":" and depth == 0:
            return after_name[:i].strip(), after_name[i + 1 :].strip()
    return after_name.strip(), ""

def top_level_binders(binders):
    """Return list of (name, type) for depth-1 (name : type) binders."""
    recs = []
    depth = 0
    start = None
    for i, ch in enumerate(binders):
        if ch == "(":
            if depth == 0:
                start = i + 1
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0 and start is not None:
                inner = binders[start:i].strip()
                recs.append(inner)
                start = None
    parsed = []
    for inner in recs:
        d = 0
        col = None
        for j, ch in enumerate(inner):
            if ch == "(":
                d += 1
            elif ch == ")":
                d -= 1
            elif ch == ":" and d == 0:
                col = j
                break
        if col is None:
            continue
        parsed.append((inner[:col].strip(), inner[col + 1 :].strip()))
    return parsed

def split_arrows(typ):
    parts, depth, last = [], 0, 0
    i = 0
    while i < len(typ):
        ch = typ[i]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif depth == 0:
            if typ.startswith("→", i) or typ.startswith("->", i):
                parts.append(typ[last:i].strip())
                i += 1 if typ.startswith("→", i) else 2
                while i < len(typ) and typ[i] == " ":
                    i += 1
                last = i
                continue
        i += 1
    parts.append(typ[last:].strip())
    return [p for p in parts if p]

def pred_in_type(typ, names):
    tokens = set(IDENT.findall(typ))
    dotted = set(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", typ))
    for n in names:
        if n in tokens or any(d == n or d.endswith("." + n) for d in dotted):
            return True
    return False

def is_prop_symbol_type(typ):
    t = typ.strip().rstrip(".")
    t = re.sub(r"\s+", " ", t)
    return t == "Prop" or t.endswith("→ Prop") or t.endswith("-> Prop")

axioms = []
for p in iter_lean_files(dirpath):
    axioms.extend(collect_axioms(p))

parsed = []
for path, line, text in axioms:
    m = re.match(r"axiom\s+([A-Za-z_][A-Za-z0-9_]*)\s*(.*)$", text)
    if not m:
        continue
    name, rest = m.group(1), m.group(2)
    binders, typ = split_colon(rest)
    parsed.append(
        dict(path=path, line=line, text=text, name=name, binders=binders, typ=typ)
    )

pred_names = {d["name"] for d in parsed if is_prop_symbol_type(d["typ"])}

hits_a, hits_b, hits_gap = [], [], []
for d in parsed:
    loc = f"{d['path']}:{d['line']}"
    if is_prop_symbol_type(d["typ"]):
        hits_a.append(f"  {loc}  {d['text']}")
        continue
    bnds = top_level_binders(d["binders"])
    arrows = split_arrows(d["typ"])
    conclusion = arrows[-1] if arrows else d["typ"]
    antes = arrows[:-1]
    prop_hyps = []
    other_prop = False
    for bname, btyp in bnds:
        if pred_in_type(btyp, pred_names):
            prop_hyps.append(("binder", bname, btyp))
        elif is_prop_symbol_type(btyp) or btyp.strip() == "Prop":
            other_prop = True
        elif INEQ.search(btyp) or "∧" in btyp or "∨" in btyp or "¬" in btyp:
            other_prop = True
    for a in antes:
        if pred_in_type(a, pred_names):
            prop_hyps.append(("ante", "", a))
        elif not pred_in_type(a, pred_names) and a:
            # data-typed antecedent (rare) vs other Prop
            if not re.match(r"^[A-Z][A-Za-z0-9_.]*$", a.strip()):
                if pred_in_type(a, pred_names):
                    pass
                else:
                    other_prop = True
    if prop_hyps and not other_prop:
        hits_b.append(f"  {loc}  {d['text']}")
        has_struct = bool(STRUCT_BINDER.search(d["binders"]))
        if has_struct and INEQ.search(conclusion):
            hits_gap.append(f"  {loc}  {d['text']}")

print("  -- 10a opaque predicate symbols --")
if hits_a:
    print("\n".join(hits_a))
else:
    print("  (none found)")
print()
print("  -- 10b axioms whose only Prop-hyps are 10a predicates --")
if hits_b:
    print("\n".join(hits_b))
else:
    print("  (none found)")
print()
print("  -- Pattern 9 gap (structure binder + inequality, guarded only by 10a) --")
if hits_gap:
    print("\n".join(hits_gap))
else:
    print("  (none found)")
print()
print(f"  Pattern 10 counts: 10a={len(hits_a)}  10b={len(hits_b)}  9-gap={len(hits_gap)}")
PY
echo

echo "=== Summary ==="
echo "Manual review required for any matches above. Each flagged axiom should:"
echo "  (a) Convert to 'theorem' with trivial proof + placeholder docstring, OR"
echo "  (b) Replace with non-vacuous content capturing the cited literature, OR"
echo "  (c) Delete and refer to literature in a comment."
echo "  Pattern 10: a 10a predicate symbol with no intro rule, or a 10b/9-gap"
echo "  axiom it uniquely guards, is a shell under Pred x := (conclusion)."
echo
echo "For a definitive vacuity check (elaboration-based), use check_axioms_lean.py."
