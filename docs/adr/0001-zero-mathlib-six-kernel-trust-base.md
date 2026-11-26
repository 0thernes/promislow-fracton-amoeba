<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# ADR 0001: Zero-Mathlib Lean 4.35.0 & Six-Kernel Palomar Trust Base

- **Status:** Accepted (`2026-11-25`)
- **Context:** Mathematical proofs verified only by a single theorem-prover kernel built atop a 2-million-line dependency tree (`mathlib4`) face both build fragility and large trusted-computing-base surface area.
- **Decision:** Implement the entire 15-theorem formal proof suite (`lean/`) from Lean 4.35.0 `Init` alone (zero Mathlib imports), using the `module` header discipline, pure structural $O(N \log N)$ merge-sort arithmetic (avoiding slow `WellFounded.fix` kernel reduction), Palomar `Challenge`/`Solution` separation (`comparator.json`), checking by Lean (`lake build`, `leanchecker`) on every push, and acceptance of the 16 comparator targets by 6 independent proof kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`). Kernel checking establishes that the proofs are complete; it does not establish that each statement matches its name (see `ERRATA.md`, 2026-11-26 statement audit).
- **Consequences:**
  - Builds cleanly in under 30 seconds on stock CI runners with zero external downloads beyond Lean 4.35.0 itself.
  - Every custom algebraic typeclass (`SimpleCommRing`, `SimpleIntegralDomain`, `TorusPt`, `IsMidpointConvex3`, `IsV4Symmetric3`) must be accompanied by explicit concrete inhabitants in `NonVacuity.lean`.
  - Transcendental real-analysis computations (3D Ronkin integrals, complex root tracking) are honestly separated into Tier-2 (`numerical-approx`) Rust & Python differential oracles rather than approximated with unsound Lean axioms.
