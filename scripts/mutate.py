#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Semantic mutation testing harness (Build Standard v1.2.0 B13).

Applies targeted algebraic mutations to python/pfa_verify/exact_core.py in an
isolated temporary copy and verifies that pytest kills 100% of mutants.
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

MUTANTS = [
    (
        "M1_group_sign_table",
        "(-1, 1, -1),",
        "(1, 1, -1),",
        "Corrupt b-coset V4 sign table in Promislow group",
    ),
    (
        "M2_coset_cocycle_entry",
        "((0, 0, 0, 2), (-1, 1, -1, 3), (0, 1, 0, 0), (-1, 0, -1, 1)),",
        "((0, 0, 0, 2), (1, 1, -1, 3), (0, 1, 0, 0), (-1, 0, -1, 1)),",
        "Corrupt b*a cocycle translation in Promislow group",
    ),
    (
        "M3_gardam_alpha_term",
        "(0, 0, -1, 0), (1, 0, -1, 0),",
        "(0, 0, 2, 0), (1, 0, -1, 0),",
        "Corrupt support exponent in Gardam alpha",
    ),
    (
        "M4_haah_k_logical_factor",
        "return 2 * (n2 - rank_mod_p(rows, p))",
        "return n2 - rank_mod_p(rows, p)",
        "Corrupt logical qudit factor 2 -> 1 in Haah rank formula",
    ),
    (
        "M5_ronkin_log_normalization",
        "return tot / (grid_n**3)",
        "return tot / (2 * grid_n**3)",
        "Corrupt Ronkin integral normalization",
    ),
    (
        "M6_discriminant_degree_sign",
        "return ang / (2.0 * math.pi), min_abs",
        "return -ang / (2.0 * math.pi), min_abs",
        "Flip sign of canonical quartic discriminant braid degree",
    ),
]


def main() -> int:
    src_core = ROOT / "python" / "pfa_verify" / "exact_core.py"
    orig_text = src_core.read_text(encoding="utf-8")

    killed = 0
    survived = 0

    for mid, old, new, desc in MUTANTS:
        if old not in orig_text:
            print(f"ERROR: mutant target not found for {mid}: {old!r}", file=sys.stderr)
            return 1
        with tempfile.TemporaryDirectory(prefix=f"pfa_mut_{mid}_") as tmp:
            tmp_root = Path(tmp)
            shutil.copytree(ROOT / "python", tmp_root / "python")
            shutil.copytree(ROOT / "tests", tmp_root / "tests")
            shutil.copytree(ROOT / "results", tmp_root / "results")
            target = tmp_root / "python" / "pfa_verify" / "exact_core.py"
            target.write_text(orig_text.replace(old, new, 1), encoding="utf-8")

            env = dict(os.environ)
            env["PYTHONPATH"] = str(tmp_root / "python")
            proc = subprocess.run(
                [
                    sys.executable,
                    "-m",
                    "pytest",
                    str(tmp_root / "tests" / "test_all.py"),
                    "-q",
                    "--tb=no",
                    "-k",
                    "not differential_rust",
                ],
                cwd=str(tmp_root),
                env=env,
                capture_output=True,
                text=True,
                check=False,
                timeout=120,
            )
            if proc.returncode != 0:
                killed += 1
                print(f"KILLED   {mid}: {desc}")
            else:
                survived += 1
                print(f"SURVIVED {mid}: {desc}")

    total = len(MUTANTS)
    print(f"\nMutation summary: {killed}/{total} mutants killed ({100.0 * killed / total:.1f}%).")
    return 1 if survived else 0


if __name__ == "__main__":
    raise SystemExit(main())
