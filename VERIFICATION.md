<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# VERIFICATION.md — Verification Architecture & Evidence Summary

This document summarizes the multi-layer verification stack backing `promislow-fracton-amoeba` v1.0.0.

## Layer 1 — Zero-Mathlib Lean 4.35.0 & Six Independent Proof Kernels
- **Toolchain:** `leanprover/lean4:v4.35.0` with `module` header discipline (`lean/lakefile.toml`).
- **Zero external dependencies:** All commutative ring, integral domain, $4\times 4$ matrix, Laurent polynomial, rational arithmetic, $S_4$ subgroup closure, and linear CA machinery is built cleanly from Lean 4 `Init` only.
- **Palomar Challenge/Solution separation:** `lean/PalomarChallenge.lean` defines the 16 public proposition contracts independently of `lean/PalomarSolution.lean`, enforced by `lean/comparator.json`.
- **Six independent kernels (GitHub Actions Ubuntu CI):**
  1. Lean 4.35.0 default kernel (`lake build`)
  2. `leanchecker-paranoid` (`Solution` and `PalomarSolution`)
  3. `lean4lean` (via `lake comparator --config comparator.json --paranoid`)
  4. `nanoda_bin` (strict `unpermitted_axiom_hard_error: true`)
  5. `con-leche --verified`
  6. `con-ron --verified`
- **Axiom purity:** `results/lean_axioms.txt` captures verbatim `#print axioms` output across all 20 audited declarations (15 theorems + master conjunction + Hensel tower + strengthened obstruction + `NonVacuity` + `AdversarialTests`). Zero `sorryAx`, zero `native_decide`, zero custom axioms.

## Layer 2 — Independent Dual-Language Exact & Numerical Oracles
- **Rust (`rust/`):** Zero external crate dependencies; 4 comprehensive unit tests (`cargo test --release`) plus JSON CLI exporter (`promislow_core summary`).
- **Python (`python/pfa_verify/exact_core.py`):** Exact arbitrary-precision `int` arithmetic and independent complex numerical solvers.
- **Differential & Property Verification (`tests/test_all.py`):**
  - Hypothesis property tests (200 random Promislow group triples; 120 random $R[P]$ pairs for $\Psi(uv)=\Psi(u)\Psi(v)$ and $V_4$-invariance).
  - Exact bit-for-bit Rust ↔ Python differential assertions across all integer invariants and $< 10^{-6}$ agreement on Ronkin/braid metrics.
  - Negative tests (`B06`), metamorphic tests (`B14`), golden snapshots (`B08`), numerical stability (`B20`), and semantic mutation testing (`scripts/mutate.py`, 6/6 = 100% mutant kill rate).

## Layer 3 — Publication & Supply-Chain Integrity
- **AMS-LaTeX paper (`paper/main.tex`):** Compiled hermetically with Tectonic 0.17.0 (`0` overfull hboxes, `0` undefined refs/cites), visually inspected page-by-page, with clean-room `dist/arxiv_submission.tar.gz` re-compilation in CI.
- **Live citation verification (`scripts/check_citations.py`):** 18/18 BibTeX entries resolved live against Crossref DOI and arXiv APIs with zero retractions.
- **Cryptographic checksums & SLSA provenance:** `MANIFEST.sha256` verified on every CI run plus `actions/attest-build-provenance@v2` attestations for the frozen PDF and arXiv tarball on pushes to `main`.
