<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# AGENTS.md — Canonical Agent Instructions for `promislow-fracton-amoeba`

This file is the canonical agent entry point (Build Standard for LLMs v1.2.0, Item A32). `CLAUDE.md`, `GEMINI.md`, and `.cursor/rules/build-standard.mdc` delegate here.

## Mission & Architecture
`promislow-fracton-amoeba` is a formally verified mathematical physics and non-commutative algebra research repository uniting:
1. **Pillar I (`ALG-035` / `ANL-063`)**: Hantzsche--Wendt / Promislow group $P$, faithful 4-band Bloch embedding $\Psi: R[P] \hookrightarrow M_4(R[x^{\pm 1}, y^{\pm 1}, z^{\pm 1}])$, universal $V_4$ determinant invariance, 8-sign-point factorizations, Gardam's 21-term unit mod 2 with 89-term integer determinant $\equiv 1 \pmod 4$, all-$m$ 2-adic Hensel tower, strengthened $2^{21}$ no-sign-lift obstruction ($P_1^2 - 31 \notin \{\pm 1\}$), and 21-neighbor $P$-equivariant reversible linear CA on $\mathbb{F}_2^P$.
2. **Pillar II (`QC-032` / `CM-016`)**: Arbitrary-ring unit-twisted non-Abelian CSS commutation, exhaustive 64-signed Haah cubic code conic discriminant classification ($\det(2Q) \in \{\pm 4, \pm 8, \pm 12\}$, $p=3$ singular $\mathbb{F}_9$ degeneration, smooth $\forall p \ge 5$), universal all-prime ($p \ge 2$, $\operatorname{char} 0$) Haah CC1 no-strings theorem via 6 pairwise $\mathbb{Z}[t]$ Bézout identities $= 2$, odd-prime torsion floor ($p \le 19$ empty, first odd-$L$ threshold at $p=23, L=11$), and first non-Abelian Hantzsche--Wendt fracton stabilizer codes.
3. **Pillar III (`CM-018` / `FLD-060`)**: Universal $V_4$-convex Ronkin origin-minimum theorem ($R(0,0,0) \le R(\mu)$), exact bipolar skin cancellation $W_x(k_y,-k_z) = -W_x(k_y,k_z)$, exact quadrilateral double-amoeba $\mathcal{A}(f) \cap \mathcal{A}(g)$ + algebraic $\mathrm{EP}_2$ Jordan nilpotency ($H \neq 0, H^2 = 0$), and Artin $B_4$ relations with full 24-element $S_4$ monodromy closure.

## Hard Rules (Non-Negotiable)
- **R1–R4 (No friction):** Commit and push straight to `main`. No PRs, no feature branches, no commit/tag signing, no blocking git hooks, no Dependabot/CodeRabbit/Copilot config. CI is informational.
- **R5 (Trust base):** Zero `sorry`, zero `admit`, zero `native_decide`, zero custom axioms in `lean/`. Every theorem in `lean/VerifyAxioms.lean` must depend strictly on a subset of `[propext, Classical.choice, Quot.sound]` and pass all 6 independent kernels via `lake comparator --config comparator.json --paranoid`.
- **R6 (Epistemic honesty):** Separate `kernel-checked`, `exact-comp`, `numerical-approx`, and `open-problem`. Overarching open conjectures (Kaplansky Unit Conjecture in char 0, general Gottschalk surjunctivity) remain explicitly OPEN. Never fabricate citations, DOIs, or test results.
- **Identity & Licensing:** Author is `Alexander Stephen Donahue` (`Independent Researcher, Spokane, WA, USA`, ORCID `0009-0006-8168-9648`, `0_0@0thernes.art`). Do NOT use "0thernes LLC" in published papers or metadata. Code is `Apache-2.0`; prose/paper/data/figures are `CC-BY-4.0`.

## One-Word Verification Commands (`justfile`)
- `just demo` — Offline quickstart across Pillars I–III
- `just rust` — Zero-dependency Rust unit tests + release summary JSON
- `just test` — Pytest + Hypothesis + differential Rust↔Python + negative + metamorphic tests
- `just mutate` — Semantic mutation testing (target: 100% mutants killed)
- `just lean` — Zero-Mathlib Lean 4.35.0 build + strict `#print axioms` audit
- `just kernels` — Local `leanchecker` + Palomar `lake comparator --paranoid`
- `just paper` — Compile `paper/main.tex` with Tectonic 0.17.0 (0 overfull hboxes, 0 undefined refs)
- `just citations` — Live Crossref DOI + arXiv + retraction audit on `paper/references.bib`
- `just audit` — Full Build Standard v1.2.0 + README axiom sync + no-LLC + version sync audit

## Directory Map
- `lean/` — Zero-Mathlib Lean 4.35.0 proof suite (`PromislowFracton/`, `Challenge.lean`, `Solution.lean`, `PalomarChallenge.lean`, `PalomarSolution.lean`, `VerifyAxioms.lean`, `comparator.json`, `formalization.yaml`)
- `rust/` — Zero-dependency Rust exact & numerical verification crate (`promislow_core`)
- `python/pfa_verify/` — Independent exact Python oracle
- `tests/` — Pytest, Hypothesis, differential, negative, metamorphic, and golden snapshot tests
- `scripts/` — Figure generation, citation audit, axiom drift check, mutation testing, Build Standard audit
- `studio/index.html` — Zero-dependency real-time 3D WebGL2 interactive laboratory
- `blueprint/index.html` — Interactive Lean 4.35.0 proof dependency DAG
- `paper/` — AMS-LaTeX manuscript source, verified `references.bib`, and 4 vector PDF figures
- `dist/` — Frozen white paper PDF + clean-room verified `arxiv_submission.tar.gz`
- `results/` — Golden verification JSONs and verbatim `lean_axioms.txt`
- `docs/` — Statement fidelity map, ADRs, FAQ/glossary, threat model, benchmarks, media
