<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# CLAIMS.md — Master Epistemic Claim Ledger

Every mathematical, algorithmic, and empirical claim made by `promislow-fracton-amoeba` v1.0.0 is catalogued below with its exact verification tier, falsifiable artifact, and explicit scope boundary (Build Standard v1.2.0 B04 / Playbook v1.3).

## Verification Tier Definitions
- **`kernel-checked`**: Formally proved in zero-Mathlib Lean 4.35.0 (`lean/`), zero `sorry`, zero `native_decide`, axioms strictly within `[propext, Classical.choice, Quot.sound]`, replayed across 6 independent kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`).
- **`exact-comp`**: Independently computed using exact arbitrary-precision integers / finite-field arithmetic in BOTH zero-dependency Rust (`rust/`) and Python (`python/pfa_verify/exact_core.py`) with automated differential assertions (`tests/test_all.py`).
- **`numerical-approx`**: Floating-point quadrature or complex root-tracking with explicit spectral gap bounds, grid-refinement stability checks, and Rust↔Python differential agreement `< 1e-6`.
- **`open-problem`**: Explicitly NOT claimed solved.

## Pillar I — Hantzsche–Wendt Group Rings & Gardam Obstructions (`ALG-035`, `ANL-063`)

| ID | Claim | Formal / Code Artifact | Tier |
|---|---|---|---|
| `T1a` | The Hantzsche–Wendt / Promislow group $P = \langle a,b \mid a^{-1}b^2a=b^{-2},\, b^{-1}a^2b=a^{-2}\rangle$ satisfies exact group axioms, is non-Abelian, and is strictly torsion-free ($\forall g \in P, n \ge 1, g^n = 1 \implies g = 1$). | `PromislowFracton.Palomar.t1a_promislow_group_torsion_free` (`lean/PromislowFracton/PromislowGroup.lean`) | `kernel-checked` |
| `T1b` | The $4$-band twisted Bloch map $\Psi : R[P] \hookrightarrow M_4(R[x^{\pm 1}, y^{\pm 1}, z^{\pm 1}])$ is an injective ring homomorphism over every commutative ring $R$. | `PromislowFracton.Palomar.t1b_faithful_four_band_bloch_homomorphism` (`lean/PromislowFracton/BlochMatrix.lean`) | `kernel-checked` |
| `T1c` | $\det_4(\Psi(u) - E I_4)$ is universally $V_4$-invariant across $(x, y^{-1}, z^{-1})$, $(x^{-1}, y, z^{-1})$, $(x^{-1}, y^{-1}, z)$, and $(0,0,0)$ is the unique $V_4$-fixed lattice point in $\mathbb{Z}^3$, forcing every unit over an integral domain to have constant Bloch determinant. | `PromislowFracton.Palomar.t1c_universal_v4_determinant_invariance` (`lean/PromislowFracton/BlochMatrix.lean`) | `kernel-checked` |
| `T1d` | Exact closed-form determinant factorizations hold at all $8$ sign points $s \in \{\pm 1\}^3$: 4 quaternionic perfect squares $(P^2 - s_x Q^2 - s_y R^2 - s_z S^2)^2$ when $s_x s_y s_z = -1$, 4-character abelian product at $(1,1,1)$, and products of two sums of squares at the other 3 points. | `PromislowFracton.Palomar.t1d_eight_sign_point_factorization` (`lean/PromislowFracton/BlochMatrix.lean`) | `kernel-checked` |
| `T1e` | Gardam's 21-term $\alpha, \beta$ satisfy $\alpha\beta = \beta\alpha = 1$ in $\mathbb{F}_2[P]$; the $\{0,1\}$-lift $\widetilde{\alpha} \in \mathbb{Z}[P]$ has an 89-term integer determinant with constant term $97$, augmentation $945$, strict $V_4$-invariance, and uniform congruence $\det \Psi(\widetilde{\alpha}) \equiv 1 \pmod 4$; geometric Hensel truncation lifts $\widetilde{\alpha}$ to $(\mathbb{Z}/2^m\mathbb{Z})[P]^\times$ for every $m \ge 1$. | `PromislowFracton.Palomar.t1e_gardam_unit_mod4_and_hensel_tower`, `hensel_geometric_identity` (`lean/PromislowFracton/GardamUnit.lean`) | `kernel-checked` |
| `T1f` | ZERO of the $2^{21} = 2{,}097{,}152$ sign lifts on Gardam's support—and more strongly, zero lifts with arbitrary even-sum $p \in \mathbb{Z}[N]$ combined with Gardam's 13-element $(q,r,s)$ support—can be units in $\mathbb{Z}[P]$, blocked by the quaternionic norm barrier $P_1^2 - 31 \notin \{\pm 1\}$ at $(1,1,-1)$ and the 8-sign-point identities. | `PromislowFracton.Palomar.t1f_exhaustive_no_sign_lift_gardam_support`, `strengthened_no_sign_lift_of_gardam_support` (`lean/PromislowFracton/GardamUnit.lean`) | `kernel-checked` |
| `T1g` | Gardam's 21-term unit induces a strictly $P$-equivariant, bijective (surjunctive & reversible) 21-neighbor linear cellular automaton $\Phi_\alpha : \mathbb{F}_2^P \to \mathbb{F}_2^P$ with exact 21-neighbor inverse $\Phi_\beta$. | `PromislowFracton.Palomar.t1g_surjunctive_reversible_linear_ca` (`lean/PromislowFracton/GardamUnit.lean`) | `kernel-checked` |

## Pillar II — All-Prime Type-II Fracton Codes & Non-Abelian HW Codes (`QC-032`, `CM-016`)

| ID | Claim | Formal / Code Artifact | Tier |
|---|---|---|---|
| `T2a` | Over any associative involutive ring $R$, $fg = gf$ and $uv = 1$ imply exact CSS symplectic commutation $(fu)(g^* v^*)^* + (gu)(-(f^* v^*))^* = 0$. | `PromislowFracton.Palomar.t2a_nonabelian_unit_twisted_css_commutation` (`lean/PromislowFracton/HaahFractons.lean`) | `kernel-checked` |
| `T2b` | All 64 signed Haah cubic codes have conic discriminants $\det(2Q) \in \{-12, -8, -4, +4, +8, +12\}$ with multiplicities $(12, 16, 4, 4, 16, 12)$; every conic is smooth for all primes $p \ge 5$; 24 codes ($m=1, \det=\pm 12$) degenerate over $\mathbb{F}_9$ at $p=3$; all 64 factor over $\mathbb{F}_4$ at $p=2$. | `PromislowFracton.Palomar.t2b_signed_haah_64_discriminant_classification` (`lean/PromislowFracton/HaahFractons.lean`) | `kernel-checked` |
| `T2c` | Haah Cubic Code 1 admits NO string logical operators in ANY prime characteristic $p \ge 2$ or characteristic $0$, via explicit $\mathbb{Z}[t]$ rational parametrization with all 6 pairwise linear Bézout identities $= 2$ (plus explicit $\mathbb{F}_4$ evaluation at $p=2$). | `PromislowFracton.Palomar.t2c_universal_all_prime_no_strings` (`lean/PromislowFracton/HaahFractons.lean`) | `kernel-checked` |
| `T2d` | For Haah CC1 in odd prime characteristic $p \ge 3$: $(1,1,1)$ is never a root, $(-1,1,-1)$ and its permutations give $k_p(L) \ge 6$ for all even $L$, zero $\mathbb{F}_p$-rational odd-order roots exist for odd $p \le 19$, and the first odd-$L$ threshold occurs at $p=23, L=11$ ($k_{23}(11)=6$), followed by $p=31, L=15$. | `PromislowFracton.Palomar.t2d_odd_prime_torsion_and_p23_threshold` (`lean/PromislowFracton/HaahFractons.lean`) | `kernel-checked` |
| `T2e` | Gardam-twisted Haah code $H_X = (f\alpha, g\alpha), H_Z = (g^*\beta^*, f^*\beta^*)$ has exact weights $(52,52)$ and $(52,56)$, commutes strictly in $\mathbb{F}_2[P]$, and fails over $\mathbb{Z}[P]$ with a 342-term even commutator defect; the intrinsic HW code $(1+a+b+ab,\, 1+x+x^{-1}+y+y^{-1}+z+z^{-1})$ commutes over every commutative ring $R[P]$ while $f_{\mathrm{HW}}$ is non-central. | `PromislowFracton.Palomar.t2e_nonabelian_hw_fracton_codes` (`lean/PromislowFracton/HaahFractons.lean`) | `kernel-checked` |

## Pillar III — 3D Non-Hermitian Amoebae, Ronkin Minima & $B_4$/$S_4$ Monodromy (`CM-018`, `FLD-060`)

| ID | Claim | Formal / Code Artifact | Tier |
|---|---|---|---|
| `T3a` | Every midpoint-convex, $V_4$-symmetric Ronkin function $R : \mathbb{Q}^3 \to \mathbb{Q}$ attains its global minimum strictly at $(0,0,0)$ ($\forall \mu, R(0,0,0) \le R(\mu)$). | `PromislowFracton.Palomar.t3a_v4_convex_ronkin_origin_minimum` (`lean/PromislowFracton/NonHermitianAmoeba.lean`) | `kernel-checked` |
| `T3b` | Haah's double-amoeba $\mathcal{A}(f) \cap \mathcal{A}(g)$ satisfies exact quadrilateral triangle inequalities containing $(r,r,r)$ for $r \ge 1$ and exiting along $(r,1,1)$ for $r \ge 4$; at any single-generator root ($f=0, g \neq 0$), the off-diagonal Dirac matrix $H$ over any integral domain is an algebraic $\mathrm{EP}_2$ ($H \neq 0, H^2 = 0$, 1D nullspace). | `PromislowFracton.Palomar.t3b_haah_amoeba_and_ep2_jordan` (`lean/PromislowFracton/NonHermitianAmoeba.lean`) | `kernel-checked` |
| `T3c` | Adjacent-band crossings $\sigma_1,\sigma_2,\sigma_3$ satisfy the Artin $B_4$ braid relations, and the Gardam crystal monodromy permutations $(1\,2)$ and $(0\,2\,1\,3)$ do not commute and generate the entire symmetric group $S_4$ of order $24$. | `PromislowFracton.Palomar.t3c_artin_b4_and_full_s4_monodromy` (`lean/PromislowFracton/NonHermitianAmoeba.lean`) | `kernel-checked` |

## Computational & Open-Problem Ledger

| ID | Claim / Quantity | Artifact | Tier |
|---|---|---|---|
| `E1` | Exact 2-adic Hensel inverse supports for $m=1\dots 6$: `[21, 169, 459, 1388, 2100, 4353]`; exact $k_p(L)$ logical qudit tables for CC1 ($p \in \{2,3,5,7,11,13,23\}$) and $m=1$ ($k_3(8)=24$). | `rust/src/lib.rs`, `python/pfa_verify/exact_core.py`, `results/exact_verification_report.json` | `exact-comp` |
| `N1` | Ronkin quadrature $R(0) \approx 4.271743 < R(0.5,0,0) \approx 4.501630 < R(0,0,0.5) \approx 4.611698$ ($N=16$); bipolar winding map $W_x(k_y,-k_z) = -W_x(k_y,k_z)$ ($\max|\mathrm{err}| = 0.0$, nonzero $42.56\%$ on $25\times 25$ gapped grid); canonical quartic discriminant braid degrees $\{-1,-3,-2,+3\}$ with gaps $> 0.48$. | `rust/src/lib.rs`, `python/pfa_verify/exact_core.py`, `results/fig3_bipolar_stats.json` | `numerical-approx` |
| `O1` | Kaplansky Unit Conjecture in characteristic $0$ ($\mathbb{Q}[P], \mathbb{Z}[P]$ over general supports); Gottschalk Surjunctivity Conjecture for non-sofic groups; asymptotic distance scaling of non-Abelian Hantzsche–Wendt fracton covers $M_L$. | Explicitly NOT claimed solved | `open-problem` |
