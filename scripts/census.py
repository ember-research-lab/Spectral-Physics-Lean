#!/usr/bin/env python3
"""census.py — kernel-level soundness census with a committed baseline.

Runs `scripts/census/Census.lean` (`#print axioms` for every SpectralPhysics
declaration) and fails if the library got WORSE than `scripts/census/baseline.json`:

  * a new project `axiom`
  * a theorem newly depending on `sorryAx`
  * a theorem newly flagged TRUE_CONCL / DECOUPLED_WITNESS (shell shapes)
  * a theorem newly depending on a `native_decide` aux axiom
  * a `SpectralPhysics/**/*.lean` file not imported by the root (orphan) and
    not in the baseline's `orphans_allowed`

Improvements (removals) are reported; re-record them with `--update`.

Usage (repo root, after `lake build`):
    python3 scripts/census.py            # check against baseline, exit 1 on regression
    python3 scripts/census.py --update   # re-record baseline.json
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CENSUS_LEAN = ROOT / "scripts" / "census" / "Census.lean"
BASELINE = ROOT / "scripts" / "census" / "baseline.json"
SHELL_FLAGS = {"TRUE_CONCL", "DECOUPLED_WITNESS"}
NATIVE_MARK = "._native."  # aux axioms native_decide emits on this toolchain
TRUST_COMPILER = {"Lean.ofReduceBool", "Lean.trustCompiler"}


def run_census() -> tuple[set[str], list[list[str]]]:
    out = subprocess.run(
        ["lake", "env", "lean", str(CENSUS_LEAN)],
        cwd=ROOT, capture_output=True, text=True,
    )
    if out.returncode != 0:
        sys.exit(f"census failed to run:\n{out.stderr[-2000:]}")
    modules, rows = set(), []
    for line in out.stdout.splitlines():
        cols = line.split("\t")
        if cols[0] == "MODULE":
            modules.add(cols[1])
        elif cols[0] in ("thm", "axiom"):
            rows.append(cols + [""] * (5 - len(cols)))
    return modules, rows


def summarize(modules: set[str], rows: list[list[str]]) -> dict[str, list[str]]:
    axioms = sorted(r[2] for r in rows if r[0] == "axiom")
    sorry, shell, native = [], [], []
    for kind, _mod, name, deps, flags in rows:
        if kind != "thm":
            continue
        dep_set = {d for d in deps.split(",") if d}
        if "sorryAx" in dep_set:
            sorry.append(name)
        if SHELL_FLAGS & set(flags.split(",")):
            shell.append(name)
        if dep_set & TRUST_COMPILER or any(NATIVE_MARK in d for d in dep_set):
            native.append(name)
    files = {
        "SpectralPhysics." + ".".join(p.relative_to(ROOT / "SpectralPhysics").with_suffix("").parts)
        for p in (ROOT / "SpectralPhysics").rglob("*.lean")
    }
    return {
        "axioms": axioms,
        "sorry_theorems": sorted(sorry),
        "shell_theorems": sorted(shell),
        "native_decide_theorems": sorted(native),
        "orphans": sorted(files - modules),
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="kernel-level soundness census with a committed baseline")
    ap.add_argument("--update", action="store_true", help="re-record baseline.json")
    args = ap.parse_args()

    current = summarize(*run_census())
    counts = {k: len(v) for k, v in current.items()}
    print("census:", json.dumps(counts))

    if args.update:
        allowed = json.loads(BASELINE.read_text()).get("orphans_allowed", []) if BASELINE.exists() else []
        current["orphans_allowed"] = allowed
        BASELINE.write_text(json.dumps(current, indent=1, ensure_ascii=False) + "\n")
        print(f"baseline written: {BASELINE.relative_to(ROOT)}")
        return 0

    baseline = json.loads(BASELINE.read_text())
    failed = False
    for key in ("axioms", "sorry_theorems", "shell_theorems", "native_decide_theorems"):
        new = sorted(set(current[key]) - set(baseline[key]))
        gone = sorted(set(baseline[key]) - set(current[key]))
        if new:
            failed = True
            print(f"REGRESSION {key}: +{len(new)}")
            for n in new:
                print(f"   + {n}")
        if gone:
            print(f"improved {key}: -{len(gone)} (run --update to record)")
    bad_orphans = sorted(set(current["orphans"]) - set(baseline["orphans_allowed"]))
    if bad_orphans:
        failed = True
        print(f"REGRESSION orphans (not imported by SpectralPhysics.lean): {bad_orphans}")
    print("FAIL" if failed else "OK")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
