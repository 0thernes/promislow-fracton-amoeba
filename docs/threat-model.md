<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Threat Model (`docs/threat-model.md`)

Per Build Standard v1.2.0 (`B36`), this threat model covers formal verification soundness, computational integrity, and software supply-chain risks for `promislow-fracton-amoeba`.

| Threat Surface | Risk | Concrete Mitigation |
|---|---|---|
| **Proof-assistant escape hatches** | Hidden `sorry`, `admit`, `native_decide`, `Lean.trustCompiler`, or custom `axiom` silently invalidating theorems | Automated `VerifyAxioms.lean` grep & diff against `results/lean_axioms.txt` in CI; `nanoda_bin` run with `unpermitted_axiom_hard_error: true`; 0 `native_decide` across repo. |
| **Specification gaming / statement drift** | Proving a weakened or vacuous theorem instead of the stated claim | Palomar `PalomarChallenge.lean` / `PalomarSolution.lean` separation verified via `lake comparator --config comparator.json --paranoid`; `NonVacuity.lean` inhabits all hypotheses; `AdversarialTests.lean` refutes 5 false variants; `docs/statement-fidelity.md` audits 1-to-1 correspondence. |
| **Single-kernel implementation bug** | Soundness bug in Lean 4's C++ kernel accepting an invalid proof term | Every push replays proof exports through 6 independent kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`). |
| **Silent bug in computational oracle** | Sign/index/normalization bug in Python or Rust producing false tables | Independent dual-language implementations (zero-dep Rust vs. Python), Hypothesis property tests, bit-for-bit differential tests, and 6/6 (100%) semantic mutation testing (`scripts/mutate.py`). |
| **Artifact / PDF tampering** | Post-build modification of frozen PDF, figures, or arXiv tarball | `MANIFEST.sha256` verified on CI + GitHub SLSA `actions/attest-build-provenance@v2` attestations on `main` + Software Heritage archival + pinned submodule in `0thernes-research-archive`. |
| **Citation hallucination / retraction** | Broken DOIs, misattributed journals, or retracted papers | Live Crossref DOI + arXiv + retraction audit (`scripts/check_citations.py`, 18/18 passed). |
| **Secret leakage** | Accidental tokens/keys in commits | `.gitleaks.toml` + report-only regex secret scan in CI; zero network credentials needed. |
