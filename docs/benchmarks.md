<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Honest Benchmarks (`docs/benchmarks.md`)

Measured on Windows 11 (ReFS Dev Drive `Z:\`), single-threaded local runs (Build Standard v1.2.0 `A37`, `B26`).

| Component | Command | Measured Wall Time | Notes |
|---|---|---|---|
| Rust unit tests (release) | `cargo test --release` | `0.22 s` | 4/4 tests passing, zero crate dependencies |
| Rust JSON summary export | `promislow_core summary` | `~0.45 s` | Includes 2-adic Hensel up to `mod 64` (4,353 terms), $N=16$ Ronkin, and 1024-step braid degrees |
| Python pytest + Hypothesis + Rust diff | `pytest tests/test_all.py -v` | `1.93 s` | 9/9 passed (200 group + 120 Bloch Hypothesis examples) |
| Semantic mutation suite | `python scripts/mutate.py` | `~14 s` | 6/6 mutants killed (100.0%) |
| Live Crossref/arXiv citation audit | `python scripts/check_citations.py` | `~9 s` | 18/18 resolved live, 0 retractions |
| Publication figures + social preview | `python scripts/make_figures.py` | `~18 s` | 4 vector PDFs + 384-step $25\times 25$ bipolar winding grid + PNG |
| AMS-LaTeX Tectonic build | `tectonic -X compile main.tex` | `~15 s` | 0 overfull hboxes, 0 undefined refs/cites |
| Lean 4.35.0 full clean build | `lake build` | See `HARDENING_LOG.md` | Pure structural $O(N \log N)$ `spMerge` optimization reduced `GardamUnit` from 71s to <10s |
