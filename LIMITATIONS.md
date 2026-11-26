<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# LIMITATIONS.md — Explicit Scope Boundaries, Threats to Validity, and Falsification Conditions

Per Build Standard v1.2.0 (`B41`, `B42`) and Playbook v1.3, this document records every known boundary of our results, distinguishes exact formal proofs from numerical computations, and states concrete conditions that would falsify our claims.

## 1. Real vs. Metaphor & Explicit Scope Limits

1. **Kaplansky's Unit Conjecture in characteristic $0$ remains OPEN.**
   - Theorem `T1f` (`t1f_exhaustive_no_sign_lift_gardam_support` and `strengthened_no_sign_lift_of_gardam_support`) rules out all $2^{21} = 2{,}097{,}152$ sign lifts $\{\pm 1\}$ supported on Gardam's 21-element support—and arbitrary even-sum $p \in \mathbb{Z}[N]$ paired with Gardam's 13-element $(q,r,s)$ support.
   - It does **not** rule out nontrivial units in $\mathbb{Z}[P]$ or $\mathbb{Q}[P]$ with larger supports, shifted supports, or integer coefficients outside $\{\pm 1\}$.
2. **2-adic Hensel tower yields a completed $\mathbb{Z}_2[[P]]$ inverse, NOT a $\mathbb{Z}[P]$ unit.**
   - Theorem `T1e` certifies exact invertibility of $\widetilde{\alpha}$ in $(\mathbb{Z}/2^m\mathbb{Z})[P]$ for every finite $m \ge 1$. Because the inverse support sizes grow exponentially (`21, 169, 459, 1388, 2100, 4353` for $m=1\dots 6$), the $2$-adic limit lives in the infinite formal power series completion $\mathbb{Z}_2[[P]]$, not the finite group ring $\mathbb{Z}[P]$.
3. **Numerical approximations in Pillar III are not interval-certified inside Lean.**
   - The $3$D Ronkin integral $R(\mu)$ (`N=16` quadrature, $R(0) \approx 4.271743$), the $25 \times 25$ spectral winding map $W_x(k_y,k_z)$ (evaluated on `npts=384` with gap filter $\min|\det| > 0.35$), and the 600–1024-step complex eigenvalue loop tracking / quartic discriminant winding degrees are floating-point computations (`numerical-approx`).
   - Because $\log|\det\Psi|$ has $1$D logarithmic nodal singularities on $\mathbb{T}^3$ where $\det\Psi = 0$, uniform trapezoidal quadrature of $R(0)$ converges at $O(1/N)$ (`4.2292` at $N=12$ vs `4.2717` at $N=16$). What IS formally proved inside Lean (`T3a`) is the universal structural law $R(0,0,0) \le R(\mu)$ for every $V_4$-symmetric midpoint-convex Ronkin function.
4. **Gottschalk's Surjunctivity Conjecture for general groups remains OPEN.**
   - Theorem `T1g` constructs a concrete bijective 21-neighbor linear CA on $\mathbb{F}_2^P$ witnessing surjunctivity for Gardam's unit on the virtually abelian (hence amenable/sofic) group $P$. It does not address non-sofic groups.
5. **Non-Abelian Hantzsche–Wendt fracton code distance scaling is open.**
   - Theorem `T2e` proves exact CSS commutation, exact stabilizer weights `(52, 52)` / `(52, 56)`, the 342-term $\mathbb{Z}[P]$ commutator defect, and ring-universal commutation of the intrinsic HW code. Computing asymptotic code-distance scaling $d(M_L)$ for large Hantzsche–Wendt $L$-covers remains open future work.
6. **Non-Abelian $S_4$ monodromy in Lean vs. numerical eigenvalue paths.**
   - Theorem `T3c` proves the exact Artin $B_4$ braid relations and that the observed permutations `[0,2,1,3]` and `[2,3,1,0]` generate all 24 elements of $S_4$. Linking those permutations to the concrete complex matrix family $\Psi(\widetilde{\alpha})(k)$ relies on floating-point Durand–Kerner root tracking and numerical quartic discriminant winding (verified differentially between Rust and Python with spectral gaps $\ge 0.4841$ and raw discriminant degrees within $10^{-14}$ of integers).

## 2. What Would Prove Us Wrong (Falsification Conditions — B42)

Any single one of the following concrete findings would immediately refute the corresponding claim and trigger an `ERRATA.md` entry:
1. **Lean kernel / axiom breach:** If `lake comparator --config comparator.json --paranoid` or any of the 6 independent kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`) rejects `PalomarSolution`, or if `#print axioms` reports any axiom outside `{propext, Classical.choice, Quot.sound}`.
2. **Sign-lift counterexample to `T1f`:** An explicit 21-tuple of signs $c_i \in \{\pm 1\}$ on Gardam's support whose product with an inverse in $\mathbb{Z}[P]$ equals $1$ (would simultaneously contradict `T1c`, `T1d`, and `T1f`).
3. **String operator counterexample to `T2c`:** A prime $p \ge 2$, nonzero $(a,b,c) \in \mathbb{Z}^3$, and $\lambda \in \overline{\mathbb{F}}_p^\times$ such that $x^a y^b z^c = \lambda$ holds identically on $V_p(1+x+y+z,\, 1+xy+yz+zx)$.
4. **Odd-$L$ Haah CC1 root for $p \le 19$:** A point $(x,y,z) \in (\mathbb{F}_p^\times)^3$ of odd multiplicative order solving Haah CC1 for any odd prime $p \in \{3,5,7,11,13,17,19\}$ (refutes `T2d`).
5. **Differential mismatch between Rust and Python:** Disagreement on any exact integer invariant (`det_terms`, `det_const_term`, `det_augmentation`, `hensel_2adic_supports`, `haah_cc1_p23_L11_k`) or deviation $> 10^{-6}$ on Ronkin / braid invariants.
6. **Retracted or fabricated citation:** Any entry in `paper/references.bib` failing live Crossref DOI / arXiv resolution or flagged as retracted.
