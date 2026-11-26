<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# REPLICATION.md — Clean-Clone Reproduction Protocol

Complete, deterministic reproduction instructions for all formal proofs, Rust and Python verifiers, test suites, figures, interactive apps, and the AMS-LaTeX white paper (Build Standard v1.2.0 `B01`, `B43`, `B44`).

## 1. Pinned Toolchains
- **Lean 4:** `leanprover/lean4:v4.35.0` (`lean/lean-toolchain`, zero Mathlib dependencies)
- **Rust:** `rustc` / `cargo` stable ($\ge 1.85$, tested on `1.94`, zero crate dependencies)
- **Python:** Python `3.11+` (tested on `3.13.12`) with pinned `requirements.txt`
- **LaTeX:** Tectonic `0.17.0` (hermetic bundle)

## 2. Clean-Clone Step-by-Step Verification

```bash
git clone https://github.com/0thernes/promislow-fracton-amoeba.git
cd promislow-fracton-amoeba
```

### Step 1: Zero-Dependency Rust Core
```bash
cd rust
cargo test --release
cargo build --release
./target/release/promislow_core summary
cd ..
```

### Step 2: Python Exact Oracle, Hypothesis, Differential & Mutation Tests
```bash
python -m venv .venv
source .venv/bin/activate   # Windows: .venv\Scripts\activate
pip install -r requirements.txt

PYTHONPATH=python python examples/quickstart_demo.py
PYTHONPATH=python python python/pfa_verify/exact_core.py
PYTHONPATH=python pytest tests/test_all.py -v
PYTHONPATH=python python scripts/mutate.py
python scripts/check_citations.py
python scripts/check_readme_axioms.py
python scripts/audit_repo.py
```

### Step 3: Zero-Mathlib Lean 4.35.0 & Six-Kernel Replay
```bash
cd lean
lake build
lake env lean VerifyAxioms.lean > /tmp/repro_axioms.txt
diff -u --strip-trailing-cr ../results/lean_axioms.txt /tmp/repro_axioms.txt
lake env leanchecker Solution
lake env leanchecker PalomarSolution
# Full 6-kernel replay (Linux with bubblewrap installed):
lake comparator --config comparator.json --paranoid
cd ..
```

### Step 4: Figures, AMS-LaTeX Paper & Clean-Room arXiv Tarball
```bash
PYTHONPATH=python python scripts/make_figures.py
cd paper
tectonic -X compile main.tex --outdir build --keep-logs --keep-intermediates
! grep -E "Overfull \\\\hbox|LaTeX Warning: Reference .* undefined" build/main.log
cd ..

# Clean-room arXiv tarball verification
mkdir -p /tmp/arxiv_verify
tar -xzf dist/arxiv_submission.tar.gz -C /tmp/arxiv_verify
(cd /tmp/arxiv_verify && tectonic -X compile main.tex)
```

### Step 5: Cryptographic Integrity & Interactive Apps
```bash
sha256sum -c MANIFEST.sha256
# Open studio/index.html or blueprint/index.html directly in any WebGL2-capable browser
```
