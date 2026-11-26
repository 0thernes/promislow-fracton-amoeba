<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Changelog

All notable changes to `promislow-fracton-amoeba` are documented in this file.
Format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/) and [Semantic Versioning](https://semver.org/).

## [Unreleased] - 2026-11-26
### Changed
- **Claim documents corrected after the 2026-11-26 statement audit** ([audit log](https://github.com/0thernes/0thernes-research-archive/blob/main/docs/reviews/2026-11-26-statement-audit.md)). `README.md`, `CLAIMS.md`, `LIMITATIONS.md`, `CITATION.cff`, `lean/formalization.yaml` and `docs/` now state what each Lean theorem proves: `T1c` is trivial at the integer sign points; `T1e` contains no Hensel statement; `T1f` shows a necessary determinant test fails, not non-invertibility; `T2c` is a monomial lemma that does not define string operators; `T2d` code dimensions are `exact-comp`; `T3a` is non-strict and has no Ronkin function; `T3b` and `T3c` define no amoeba, braid group or monodromy. "Brand-new", "first", "strengthened" and "fracton" claims were removed.
- The unit conjecture is now stated as false over $\mathbb{C}$ (Gardam, arXiv:2312.05240); prior work by Passman (arXiv:2108.06570), Tabei (arXiv:2608.00103), Kim (arXiv:1202.0052) and others is credited.
- Six-kernel wording narrowed to the 16 comparator targets.
- `ERRATA.md` lists the errors that remain in the frozen paper and the known issues in the Lean code. No Lean, paper, data or CI file was changed; `MANIFEST.sha256` was updated for `lean/formalization.yaml`.

## [1.0.0] - 2026-11-25
### Added
- **Zero-Mathlib Lean 4.35.0 Formalization (`lean/`):** 15 headline theorems (`T1a`–`T3c`), universal `hensel_geometric_identity`, `strengthened_no_sign_lift_of_gardam_support`, `NonVacuity.lean`, `AdversarialTests.lean`, Palomar Challenge/Solution separation (`comparator.json`), and `VerifyAxioms.lean` audited across 6 independent proof kernels.
- **Zero-Dependency Rust Engine (`rust/`):** Fast exact Promislow group ring, 89-term integer determinant, 2-adic Hensel lift tower, Haah prime-characteristic degeneracy solver, 3D Ronkin integrator, and canonical quartic discriminant braid degree calculator.
- **Independent Python Exact Oracle & Verification Suite (`python/`, `tests/`, `scripts/`):** Exact integer oracle, Hypothesis property suite, differential Rust↔Python tests, negative/metamorphic/golden tests, 6/6 semantic mutation harness, live Crossref/arXiv citation auditor, and Build Standard v1.2.0 auditor.
- **Interactive WebGL2 Studio & Proof Blueprint (`studio/index.html`, `blueprint/index.html`):** Real-time 4-mode 3D WebGL2 laboratory and interactive Lean 4.35.0 theorem dependency DAG deployed to GitHub Pages.
- **AMS-LaTeX White Paper (`paper/main.tex`, `dist/`):** Publication-grade manuscript with 4 vector PDF figures, zero overfull hboxes, 18 live-verified non-retracted citations, frozen PDF, and clean-room verified `arxiv_submission.tar.gz`.
- **Full Governance & Integrity Suite:** Build Standard v1.2.0 (`repo.yaml`, 90/90 evaluated), Playbook v1.3 compliance, dual licensing (`Apache-2.0` code / `CC-BY-4.0` prose), 3 full hardening cycles logged in `HARDENING_LOG.md`, `MANIFEST.sha256`, and SLSA provenance workflow.
