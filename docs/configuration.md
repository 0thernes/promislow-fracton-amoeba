<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Environment & Configuration (`A33`)

`promislow-fracton-amoeba` executes strictly offline with **zero required environment variables, secrets, or external network API keys**.

## Pinned Toolchains & Lockfiles

| Component | Source of Truth | Notes |
|---|---|---|
| Lean 4 Formalization | `lean/lean-toolchain` (`leanprover/lean4:v4.35.0`), `lean/lakefile.toml`, `lean/lake-manifest.json` | Zero Mathlib; verified via `lake build` and 6-kernel Palomar Comparator |
| Rust Exact & Numerical Engine | `rust/Cargo.toml`, `rust/Cargo.lock` | Zero-unsafe exact arithmetic & quadrature crate |
| Python Verification & Tests | `pyproject.toml`, `requirements.txt` | Runs `pytest`, `ruff`, `mypy`, `scripts/audit_repo.py`, `scripts/mutate.py` |
| AMS-LaTeX White Paper | `paper/main.tex`, `paper/references.bib` | Compiled offline with Tectonic |

## Optional Runtime Variables
- `PFA_SEED`: Optional integer seed override for randomized property tests (default: deterministic fixed seeds in `tests/test_all.py`).
- Standard `PATH` entries for `lake`/`lean` (`~/.elan/bin`), `cargo` (`~/.cargo/bin`), and `tectonic`.
