<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# DEVIATIONS.md — Intentional Deviations from Build Standard v1.2.0

Every Build Standard v1.2.0 item marked `n/a` in `repo.yaml` is justified explicitly below:

- **`A34` (Runtime observability/health endpoints):** `n/a` — This is a deterministic mathematical research, formal verification, and static WebGL2 repository, not a long-running network service (`service: false`).
- **`A35` (Database migrations & backups):** `n/a` — No mutable database or schema migrations; immutable research artifacts are preserved via Git, GitHub Releases, Software Heritage Save Code Now, and `0thernes-research-archive`.
- **`A40` / `B33` / `B34` (Shipped AI model weights, held-out ML splits, LLM runtime evals):** `n/a` — Repository contains zero shipped AI models, zero ML training pipelines, and zero runtime LLM API calls (`ai: false`, `ml: false`). AI research assistance during authoring is transparently disclosed in `paper/main.tex`, `README.md`, and `lean/formalization.yaml`.
- **`A45` (Personal data / PII handling):** `n/a` — Zero personal data is collected, stored, transmitted, or logged (`personal_data: false`).
- **`B19` (Concurrency / data-race testing):** `n/a` — All Rust, Python, Lean, and WebGL2 code is single-threaded and deterministic (`concurrent: false`).
- **`B21` (Distributed failure injection / chaos engineering):** `n/a` — Not a distributed runtime service (`service: false`).
- **`B23` / `B25` (TLA+ protocol model checking & CBMC C bounded model checking):** `n/a` — Core algebraic theorems are proved directly by interactive theorem proving (`B22`, Lean 4.35.0 across 6 independent kernels) and the native verifier is memory-safe safe Rust (`B24`) rather than unsafe C/C++.
- **`B28`–`B32` (Frequentist statistical hypothesis tests, p-values, multi-seed randomized trials, clinical pre-registration):** `n/a` — Claims are deterministic mathematical theorems (`kernel-checked`), exact integer computations (`exact-comp`), and deterministic quadrature/root-tracking (`numerical-approx`), not stochastic statistical experiments.
