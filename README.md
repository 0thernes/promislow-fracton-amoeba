<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Promislow–Fracton–Amoeba

**Hantzsche–Wendt Group Rings, All-Prime Type-II Fracton Codes, and 3D Non-Hermitian $B_4$ Eigenvalue Monodromy — A Zero-Mathlib Six-Kernel Formalization.**

*The line above is the title of the v1.0.0 paper. It names the topics, not formalized properties: no fracton code property, braid group $B_4$ or monodromy is defined in Lean. In plain terms, this repository is a kernel-checked Lean formalization of known facts, elementary identities and finite computations about the Hantzsche–Wendt group ring, Haah's CC1 curve and $S_4$. A statement audit on 2026-11-26 found that several earlier headline claims went beyond the Lean statements; they are corrected below and listed in [`ERRATA.md`](ERRATA.md).*

[![CI Status](https://github.com/0thernes/promislow-fracton-amoeba/actions/workflows/ci.yml/badge.svg)](https://github.com/0thernes/promislow-fracton-amoeba/actions/workflows/ci.yml)
[![Pages Studio & Blueprint](https://github.com/0thernes/promislow-fracton-amoeba/actions/workflows/pages.yml/badge.svg)](https://0thernes.github.io/promislow-fracton-amoeba/studio/)
[![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0%20(Zero%20Mathlib)-0ea5e9.svg)](lean/lean-toolchain)
[![Six Kernels](https://img.shields.io/badge/Proof%20Kernels-6%20Independent-16a34a.svg)](lean/comparator.json)
[![Code License](https://img.shields.io/badge/Code-Apache%202.0-blue.svg)](LICENSE-CODE)
[![Paper & Data License](https://img.shields.io/badge/Paper%20%26%20Data-CC--BY--4.0-orange.svg)](LICENSE)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0006--8168--9648-a6ce39.svg)](https://orcid.org/0009-0006-8168-9648)

<p align="center">
  <img src="docs/media/social-preview.png" alt="Promislow-Fracton-Amoeba 4-Band B4 Eigenvalue Braid" width="880">
</p>

> **Interactive Apps (GitHub Pages):** [**Open 3D WebGL2 Studio**](https://0thernes.github.io/promislow-fracton-amoeba/studio/) · [**Open Lean 4.35.0 Proof Blueprint DAG**](https://0thernes.github.io/promislow-fracton-amoeba/blueprint/) · [**Read 10-Page White Paper (PDF)**](dist/Donahue_2026_promislow_fracton_amoeba.pdf)

---

## What Is Proved Here?

The repository contains 15 Lean theorems (`T1a`–`T3c`) about the torsion-free Hantzsche–Wendt (Promislow) group $P = \langle a,b \mid a^{-1}b^2a = b^{-2},\, b^{-1}a^2b = a^{-2} \rangle$, its $4 \times 4$ Bloch representation $\Psi$, Haah's cubic code 1 (CC1) curve, and the symmetric group $S_4$. Each item below says what the Lean statement proves, what rests on Rust/Python computation or on a paper argument, and which prior work it builds on. "Kernel-checked" means checked by Lean (`lake build`, `leanchecker`); the 16 comparator targets in [`lean/comparator.json`](lean/comparator.json) were also accepted by 6 independent kernels.

**Prior work.** Gardam found a non-trivial unit in $\mathbb{F}_2[P]$ (Annals 2021, arXiv:2102.11818); the 21-term unit used here is his. Gardam, arXiv:2312.05240, showed that $\mathbb{C}[P]$ has non-trivial units, so the unit conjecture is false in characteristic 0. Whether $\mathbb{Z}[P]$ or $\mathbb{Q}[P]$ has non-trivial units remains open. The $4 \times 4$ matrix representation of the group ring and the determinants of units in it are discussed by Passman, arXiv:2108.06570. Tabei, arXiv:2608.00103 (preprint), shows that no unit of $\mathbb{Z}[P]$ supported in $B(4)$ has nontrivial reduction mod 2. The qubit no-strings property of CC1 is Haah's (arXiv:1101.1962), and Kim, arXiv:1202.0052, gives no-string conditions for qudit cubic codes.

1. **Pillar I — group ring of $P$:**
   - **`T1a` (kernel-checked; known result):** A concrete multiplication on $\mathbb{Z}^3 \times \{e,a,b,ab\}$ satisfies the group axioms and the two defining relations, and the resulting group is non-abelian and torsion-free. The isomorphism with the presented group is not formalized.
   - **`T1b` (kernel-checked; known result):** Over every commutative ring in the repository's ring class, $4 \times 4$ Bloch evaluation at a point with given inverses preserves $1$, $+$ and $\times$. A separately defined formal coefficient map (`psiFormal`) is injective; no lemma links it to the evaluation map, so faithfulness of the evaluation map is not proved.
   - **`T1c` (kernel-checked, but weaker than its name):** The determinant statement is quantified over integer torus points, which are the 8 sign points, where the $V_4$ action is the identity; this part is a tautology. The second part states that $(0,0,0)$ is the only lattice point fixed by the $V_4$ action on $\mathbb{Z}^3$. $V_4$-invariance of $\det(\Psi(u)-EI_4)$ as a Laurent polynomial and constancy of unit determinants are paper arguments, not Lean theorems.
   - **`T1d` (kernel-checked):** For all integers $P, Q, R, S$, the determinant of a separately defined sign-point matrix (`blochAtSign`) at each of the 8 points $(\pm1,\pm1,\pm1)$ equals a stated product of linear forms, a square, or a product of sums of two squares. No lemma links `blochAtSign` to the Bloch evaluation map.
   - **`T1e` (kernel-checked; known unit):** Gardam's 21-term $\alpha, \beta$ satisfy $\alpha\beta = \beta\alpha = 1$ in $\mathbb{F}_2[P]$. The repository's sparse Laurent determinant of the $\{0,1\}$-lift $\widetilde{\alpha}$ has 89 terms, constant term 97 and coefficient sum 945; it is $V_4$-invariant and $\equiv 1 \pmod 2$ and $\pmod 4$. Despite the theorem's name, it contains no Hensel statement. Invertibility of $\widetilde{\alpha}$ in $(\mathbb{Z}/2^m\mathbb{Z})[P]$ is standard lifting (2 is nilpotent mod $2^m$); Lean has only the generic identity `hensel_geometric_identity`, which is not applied to Gardam's unit. The inverse support sizes `21, 169, 459, 1388, 2100, 4353` for $m=1\dots 6$ are Rust/Python computations (`exact-comp`).
   - **`T1f` (kernel-checked; necessary condition only):** For every $\pm 1$ choice of the 21 coefficients on Gardam's support, the 8 sign-point determinants are not all $\pm 1$; the companion lemma `strengthened_no_sign_lift_of_gardam_support` allows a more general $p$-part. The key step is $P_1^2 - 31 \notin \{\pm 1\}$ at $(1,1,-1)$. Lean does not prove that these lifts are non-units in $\mathbb{Z}[P]$: the step "unit implies all sign-point determinants are $\pm 1$" needs determinant multiplicativity and the link to the evaluation map, which are paper arguments. The non-unit conclusion for all these lifts is implied by Tabei, arXiv:2608.00103.
   - **`T1g` (kernel-checked; standard construction):** Convolutions by $\alpha$ and $\beta$ on configurations $P \to \mathbb{F}_2$ are mutually inverse, and convolution by $\alpha$ commutes with left shifts. This is the reversible cellular automaton attached to the unit. $P$ is virtually abelian, hence sofic, so surjunctivity on $P$ is already known.

2. **Pillar II — Haah's CC1 curve and CSS pairs over $\mathbb{Z}[P]$:**
   - **`T2b` (kernel-checked; finite enumeration):** On the 64 sign tuples, the defined function `signedHaahConicDet` takes values in $\{\pm 4, \pm 8, \pm 12\}$ with counts $(12, 16, 4, 4, 16, 12)$, none divisible by a prime $p \ge 5$; Lean also checks a mod-3 identity and an $\mathbb{F}_4$ factorization. The map from signed codes to conic discriminants is a definition, and the gauge classes, the 24-code degeneration at $p=3$ and $k_3(8)=24$ are not in the Lean statement ($k_3(8)$ is `exact-comp`).
   - **`T2c` (kernel-checked; elementary algebraic lemma):** Let $K$ be an integral domain with $2 \neq 0$ in which $P_x = -(1+3t+t^2)$, $P_y = 1+t-t^2$ and $P_z = -1+t+t^2$ each have a root, and $D = 1+t+t^2$. If a monomial $P_x^a P_y^b P_z^c D^{-a-b-c}$, cleared of negative powers, is a nonzero constant for every $t \in K$, then $a=b=c=0$; an analogous statement holds on one explicit line over $\mathbb{F}_4$. The three quadratics have discriminant 5, so the hypotheses fail over $\mathbb{Z}$, $\mathbb{Q}$ and $\mathbb{F}_p$ with $p \equiv \pm 2 \pmod 5$; those cases need an extension field. Characteristic 2 is covered only by the one $\mathbb{F}_4$ line. String logical operators are not defined in Lean; the reduction from "no string operators" to this monomial condition is on paper only. Compare Haah (arXiv:1101.1962), Kim (arXiv:1202.0052) and Dua–Kim–Cheng–Williamson (arXiv:1908.08049).
   - **`T2d` (kernel-checked search; code dimensions are `exact-comp`):** $(1,1,1)$ is not a CC1 point for odd $p \ge 3$, and $(-1,1,-1)$ is. No $(x,y,z) \in (\mathbb{F}_p^\times)^3$ of odd order lies on the CC1 curve for $p = 3, 5, 7, 11, 13, 17, 19$; such points exist for $p = 23$ and $31$. So $p=23$ is the first odd prime with an $\mathbb{F}_p$-rational odd-order CC1 point. No code dimension is defined in Lean; $k_{23}(11)=6$, $k_p(L) \ge 6$ for even $L$, and the $6p$ jumps at $L=2p$ are Rust/Python computations. Points over extension fields are not covered.
   - **`T2a`, `T2e` (kernel-checked; CSS stabilizer pairs):** In any associative structure with the listed involution axioms, $fg = gf$ and $uv = 1$ imply the CSS commutation identity. The identity also holds for $u = 1$, so commutation does not depend on Gardam's unit. For Haah's $f, g$ on $P$ twisted by Gardam's $\alpha, \beta$, the four check polynomials have 52, 52, 52 and 56 terms mod 2; the commutator vanishes mod 2 and has 342 terms over $\mathbb{Z}$. A second explicit pair commutes in $\mathbb{Z}[P]$ and is not central. No distance, logical-qubit count or fracton property is formalized. Related constructions: Tian–Samperton–Wang (arXiv:1812.02101) generalize Haah codes to 3-manifolds, and Lin–Pryadko (arXiv:2306.16400) build codes over arbitrary, generally non-abelian, finite groups.

3. **Pillar III — convexity and $S_4$ facts, with numerical companions:**
   - **`T3a` (kernel-checked; elementary convexity):** Every $R : \mathbb{Q}^3 \to \mathbb{Q}$ that is midpoint convex and invariant under the three double sign flips satisfies $R(0,0,0) \le R(x,y,z)$. The minimum is not strict (a constant function satisfies the hypotheses). No Ronkin function or real-valued function appears in Lean. The Ronkin values ($R(0) \approx 4.272$ for $\Psi(\widetilde{\alpha})$) and the bipolar winding symmetry $W_x(k_y,-k_z) = -W_x(k_y,k_z)$ on a $25 \times 25$ grid are `numerical-approx`.
   - **`T3b` (kernel-checked; integer-point checks):** The defined amoeba inequality predicates hold at $(r,r,r)$ for integers $r \ge 1$, and the linear one fails at $(r,1,1)$ for $r \ge 4$. No amoeba (image under $\mathrm{Log}|\cdot|$) is defined, so this is not a characterization of $\mathcal{A}(f)\cap\mathcal{A}(g)$. Over any integral domain, $\begin{pmatrix} 0 & 0 \\ g & 0 \end{pmatrix}$ with $g \neq 0$ is nonzero, squares to $0$, and its kernel vectors have first coordinate $0$.
   - **`T3c` (kernel-checked; textbook $S_4$ facts):** In a 4-tuple model of $S_4$, the adjacent transpositions satisfy the braid relations; `(1 2)` and `(0 2 1 3)` do not commute, the first squares to the identity, the second has order dividing 4, and together they generate all 24 permutations. No braid group $B_4$ is defined. That these two permutations are the monodromies of $\Psi(\widetilde{\alpha})(k)$ along torus cycles, and the discriminant braid degrees $\{-1, -3, -2, +3\}$, are `numerical-approx`.

---

## Quickstart (Clean Clone)

```bash
git clone https://github.com/0thernes/promislow-fracton-amoeba.git
cd promislow-fracton-amoeba

# 1. Zero-dependency Rust core (0.22s unit tests + JSON summary)
cd rust && cargo test --release && cargo run --release -- summary && cd ..

# 2. Independent Python exact oracle, Hypothesis, differential Rust<->Python, & 100% mutation suite
python -m venv .venv && source .venv/bin/activate   # Windows: .venv\Scripts\activate
pip install -r requirements.txt
PYTHONPATH=python python examples/quickstart_demo.py
PYTHONPATH=python pytest tests/test_all.py -v
PYTHONPATH=python python scripts/mutate.py

# 3. Zero-Mathlib Lean 4.35.0 formal proof build, axiom audit & leanchecker
cd lean && lake build && lake env lean VerifyAxioms.lean && lake env leanchecker PalomarSolution && cd ..

# 4. Interactive 3D WebGL2 Studio & Proof Blueprint (zero dependencies, runs offline)
# Open studio/index.html or blueprint/index.html in any modern browser.
```

---

## Verbatim Lean 4.35.0 `#print axioms` Audit (`results/lean_axioms.txt`)

The 14 Lean files contain no `admit`, no `native_decide`, no custom axioms and no Mathlib imports. The proof files contain no `sorry`; `lean/PalomarChallenge.lean` is the comparator challenge template and intentionally has `sorry` bodies (it is outside the default build targets). The output below is checked against [`results/lean_axioms.txt`](results/lean_axioms.txt) by `scripts/check_readme_axioms.py`. CI checks the proofs with Lean (`lake build`, `leanchecker`); the 16 comparator targets in `lean/comparator.json` were also accepted by 6 independent kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche --verified`, `con-ron --verified`) via `lake comparator --config comparator.json --paranoid`. A clean axiom report shows that the proofs are complete, not that each statement says what its name suggests; see the item list above.

```text
'PromislowFracton.Palomar.t1a_promislow_group_torsion_free' depends on axioms: [propext, Classical.choice, Quot.sound]
'PromislowFracton.Palomar.t1b_faithful_four_band_bloch_homomorphism' depends on axioms: [propext, Quot.sound]
'PromislowFracton.Palomar.t1c_universal_v4_determinant_invariance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PromislowFracton.Palomar.t1d_eight_sign_point_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'PromislowFracton.Palomar.t1e_gardam_unit_mod4_and_hensel_tower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PromislowFracton.Palomar.t1f_exhaustive_no_sign_lift_gardam_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PromislowFracton.Palomar.t1g_surjunctive_reversible_linear_ca' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PromislowFracton.Palomar.t2a_nonabelian_unit_twisted_css_commutation' does not depend on any axioms
'PromislowFracton.Palomar.t2b_signed_haah_64_discriminant_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PromislowFracton.Palomar.t2c_universal_all_prime_no_strings' depends on axioms: [propext, Classical.choice, Quot.sound]
'PromislowFracton.Palomar.t2d_odd_prime_torsion_and_p23_threshold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PromislowFracton.Palomar.t2e_nonabelian_hw_fracton_codes' depends on axioms: [propext]
'PromislowFracton.Palomar.t3a_v4_convex_ronkin_origin_minimum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PromislowFracton.Palomar.t3b_haah_amoeba_and_ep2_jordan' depends on axioms: [propext, Classical.choice, Quot.sound]
'PromislowFracton.Palomar.t3c_artin_b4_and_full_s4_monodromy' depends on axioms: [propext]
'PromislowFracton.Palomar.prove_all_promislow_fracton_theorems' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PromislowFracton.hensel_geometric_identity' depends on axioms: [propext]
'PromislowFracton.strengthened_no_sign_lift_of_gardam_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PromislowFracton.NonVacuity.nonvac_all_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]
'PromislowFracton.Adversarial.all_adversarial_refutations' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## Honest Epistemic Boundaries

- **What this repository does not solve:** No result here answers a published open question. The unit conjecture is false over $\mathbb{C}$ (Gardam, arXiv:2312.05240, for this group $P$). Whether $\mathbb{Z}[P]$ or $\mathbb{Q}[P]$ has non-trivial units for unrestricted supports, Gottschalk's surjunctivity conjecture for non-sofic groups, and the distance scaling $d(M_L)$ of the CSS pairs on Hantzsche–Wendt covers remain open. See [`CLAIMS.md`](CLAIMS.md) and [`LIMITATIONS.md`](LIMITATIONS.md).
- **Separated verification tiers:** Floating-point 3D Ronkin integrals, $25 \times 25$ bipolar winding grids, and 600–1024-step complex eigenvalue loop tracks are tagged `numerical-approx` and compared between Rust and Python (`< 1e-6`). Code dimensions $k_p(L)$ and 2-adic inverse supports are `exact-comp`. Neither is part of the Lean theorems.
- **Self-assessed research preprint:** Not externally peer-reviewed; no external DOI or journal publication is claimed. The frozen paper PDF predates the 2026-11-26 statement audit; its corrections are in [`ERRATA.md`](ERRATA.md).

---

## Repository Map

| Path | Description |
|---|---|
| [`lean/`](lean/) | Zero-Mathlib Lean 4.35.0 formalization (15 theorems + `NonVacuity` + `AdversarialTests` + Palomar `comparator.json` + `formalization.yaml`) |
| [`rust/`](rust/) | Zero-dependency Rust exact & numerical engine (`promislow_core`) |
| [`python/pfa_verify/`](python/pfa_verify/) | Independent Python exact arbitrary-precision oracle |
| [`tests/`](tests/) | Pytest, Hypothesis property tests, differential Rust↔Python, negative, metamorphic & golden tests |
| [`scripts/`](scripts/) | Vector figures, 100% semantic mutation harness, live citation audit, axiom drift & Build Standard auditor |
| [`studio/index.html`](studio/index.html) | Zero-dependency real-time 4-mode 3D WebGL2 interactive laboratory |
| [`blueprint/index.html`](blueprint/index.html) | Interactive Lean 4.35.0 theorem dependency DAG |
| [`paper/`](paper/) & [`dist/`](dist/) | 10-page AMS-LaTeX white paper (`0` warnings, `18/18` live-verified citations), frozen PDF & clean-room arXiv tarball |
| [`CLAIMS.md`](CLAIMS.md), [`LIMITATIONS.md`](LIMITATIONS.md), [`ERRATA.md`](ERRATA.md), [`REPLICATION.md`](REPLICATION.md), [`HARDENING_LOG.md`](HARDENING_LOG.md) | Claim ledger, scope limits and falsification conditions, corrections from the 2026-11-26 statement audit, replication protocol, and hardening log |

---

## Author, AI Disclosure & Citation

- **Author:** Alexander Stephen Donahue · Independent Researcher, Spokane, WA, USA · ORCID [`0009-0006-8168-9648`](https://orcid.org/0009-0006-8168-9648) · `0_0@0thernes.art` · [0thernes.art](https://0thernes.art)
- **Maintenance Status:** Actively maintained (`v1.0.0`, archival-grade research release).
- **AI Assistance:** Google Antigravity / Gemini assisted under continuous human supervision with Lean 4.35.0 proof engineering, Rust/Python verification, WebGL2 studio authoring, figure generation, and manuscript drafting. The Lean proofs are kernel-checked as described above; what each Lean statement covers is stated in the item list and in [`CLAIMS.md`](CLAIMS.md). See also [`lean/formalization.yaml`](lean/formalization.yaml).
- **License:** Code under [Apache-2.0](LICENSE-CODE); scholarly prose, white paper, figures, and data under [CC-BY-4.0](LICENSE).
- **Cite:** See [`CITATION.cff`](CITATION.cff) and [`CITATION.bib`](CITATION.bib).
