<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Contributing

Contributions, independent reproductions, mathematical counterexamples, and formalization improvements are warmly welcomed.

## Standards for Contributions
1. **Formal proof hygiene:** Zero `sorry`, zero `admit`, zero `native_decide`, zero custom axioms in `lean/`. Every theorem in `lean/VerifyAxioms.lean` must remain strictly within `[propext, Classical.choice, Quot.sound]` and pass `lake comparator --config comparator.json --paranoid`.
2. **Test & mutation discipline:** Run `just test`, `just mutate` (100% mutant kill rate), `just rust`, and `just audit`.
3. **Dual licensing:** Code contributions are licensed under `Apache-2.0`; scholarly prose, documentation, and figures under `CC-BY-4.0`. Include SPDX headers on new source files.
4. **Epistemic honesty:** Clearly label verification tiers (`kernel-checked`, `exact-comp`, `numerical-approx`, `open-problem`) in `CLAIMS.md` and `paper/main.tex`.
5. **Finding taxonomy:** Tag issues using the 10-class Build Standard taxonomy (`bug`, `error`, `issue`, `problem`, `concern`, `dilemma`, `conflict`, `gap`, `hole`, `blindspot`).
