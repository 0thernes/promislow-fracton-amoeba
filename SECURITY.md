<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Security Policy

## Supported Versions
| Version | Supported |
|---|---|
| `1.0.x` | Yes |

## Scope & Threat Model
`promislow-fracton-amoeba` is an offline mathematical research, formal verification (Lean 4.35.0), Rust/Python computational oracle, and static client-side WebGL2 visualization repository. It runs no network servers, stores no user credentials, and processes no personal data. See [`docs/threat-model.md`](docs/threat-model.md) for the full formal-trust-base and supply-chain threat model.

## Reporting a Vulnerability or Proof-Soundness Defect
If you discover a soundness defect, axiom leak, build-supply-chain issue, or security concern, please report it directly to:
- **Email:** `0_0@0thernes.art`
- **Maintainer:** Alexander Stephen Donahue (`@0thernes`, ORCID `0009-0006-8168-9648`)

We acknowledge reports within 72 hours and publish transparent post-mortems in [`ERRATA.md`](ERRATA.md).
