#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Verify that README.md reproduces results/lean_axioms.txt verbatim without drift."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main() -> int:
    axioms_file = ROOT / "results" / "lean_axioms.txt"
    readme_file = ROOT / "README.md"
    if not axioms_file.exists():
        print(f"ERROR: missing {axioms_file}", file=sys.stderr)
        return 1
    if not readme_file.exists():
        print(f"ERROR: missing {readme_file}", file=sys.stderr)
        return 1

    axioms_text = axioms_file.read_text(encoding="utf-8").strip().replace("\r\n", "\n")
    readme_text = readme_file.read_text(encoding="utf-8").replace("\r\n", "\n")

    for forbidden in ("sorryAx", "_native", "Lean.ofReduceBool", "Lean.trustCompiler"):
        if forbidden in axioms_text:
            print(f"ERROR: forbidden axiom {forbidden!r} found in {axioms_file}", file=sys.stderr)
            return 1

    if axioms_text not in readme_text:
        print("ERROR: README.md does not contain verbatim results/lean_axioms.txt block!", file=sys.stderr)
        return 1

    print(f"OK: README.md matches results/lean_axioms.txt verbatim ({len(axioms_text.splitlines())} lines).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
