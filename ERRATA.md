<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# ERRATA.md

Pre-release bugs and fixes from the three hardening cycles are logged in [`HARDENING_LOG.md`](HARDENING_LOG.md). Post-release corrections are recorded below with location, affected claim and whether a theorem statement is affected.

## 2026-11-26 statement audit

An independent statement audit of commit `c829ab8` (audit log: <https://github.com/0thernes/0thernes-research-archive/blob/main/docs/reviews/2026-11-26-statement-audit.md>) rebuilt the Lean project (pass, axioms as reported) and compared each claim with the Lean statements and the literature. The public claim documents (`README.md`, `CLAIMS.md`, `LIMITATIONS.md`, `CITATION.cff`, `lean/formalization.yaml`, `docs/`) were corrected in place. The frozen paper (`paper/main.tex`, `dist/Donahue_2026_promislow_fracton_amoeba.pdf`, `dist/arxiv_submission.tar.gz`) and the Lean code were not changed; their errors are listed here. Line numbers refer to `paper/main.tex` at commit `c829ab8`.

### Errors in the frozen paper

1. **Status of the unit conjecture in characteristic 0.**
   - Where: abstract, `paper/main.tex:105-106`; introduction, lines 117-124; claims table row `O1`, line 193.
   - What is wrong: the paper says Kaplansky's unit conjecture in characteristic 0 remains open. Gardam, arXiv:2312.05240 ("Non-trivial units of complex group rings"), showed that $\mathbb{C}[P]$ has non-trivial units for this group $P$, so the conjecture is false in characteristic 0. The reference is not cited.
   - Correction: "The unit conjecture is false over $\mathbb{C}$ (Gardam, arXiv:2312.05240). Whether $\mathbb{Z}[P]$ or $\mathbb{Q}[P]$ has non-trivial units remains open."
   - Affects a theorem statement: no (affects the stated open-problem boundary).
2. **`T1c`: $V_4$ determinant invariance and constant unit determinants.**
   - Where: abstract, lines 74-76; Theorem 2.2 (`thm:t1cd`) items (1)-(2), lines 240-254; claims table row `T1c`, line 177.
   - What is wrong: the theorem is tagged kernel-checked, but the Lean determinant statement is quantified over integer torus points, which are the 8 sign points where the $V_4$ action is the identity, so it is a tautology. Neither $V_4$-invariance of the Laurent determinant nor constancy of unit determinants is in Lean.
   - Correction: items (1)-(2) are paper-level arguments. The kernel-checked part is the integer sign-point statement and the fact that $(0,0,0)$ is the only $V_4$-fixed point of $\mathbb{Z}^3$.
   - Affects a theorem statement: yes (the kernel-checked tag of Theorem 2.2 (1)-(2)).
3. **`T1e`: the 2-adic Hensel tower.**
   - Where: abstract, lines 77-80 ("unexpected mod-4 congruence ... constructive 2-adic Hensel tower"); Theorem `thm:t1ef` item (1), lines 282-294; section text, line 275; claims table row `T1e`, line 179.
   - What is wrong: the Hensel tower is tagged kernel-checked, but the Lean theorem `t1e_gardam_unit_mod4_and_hensel_tower` contains no Hensel statement, and `hensel_geometric_identity` is never applied to Gardam's unit. Invertibility modulo $2^m$ of a lift of a mod-2 unit is standard (2 is nilpotent mod $2^m$), not unexpected.
   - Correction: the kernel-checked part is the determinant data (89 terms, constant term 97, coefficient sum 945, $V_4$-invariant, $\equiv 1 \bmod 2$ and $\bmod 4$). The lifting is standard; the inverse supports are `exact-comp`.
   - Affects a theorem statement: yes (Theorem `thm:t1ef` (1), last sentence).
4. **`T1f`: sign lifts of Gardam's support.**
   - Where: abstract, lines 80-82 ("ruling out all $\pm 1$ lifts"); Theorem `thm:t1ef` item (2), lines 295-313; claims table row `T1f`, line 180; section title, line 198.
   - What is wrong: Lean proves that the 8 sign-point determinants are not all $\pm 1$, a necessary condition for a unit. It does not prove that the lifts are non-units, since determinant multiplicativity and the link between `blochAtSign` and $\Psi$ are not formalized. The non-unit conclusion is implied by an earlier preprint that is not cited: Tabei, arXiv:2608.00103, shows that no unit of $\mathbb{Z}[P]$ supported in $B(4)$ has nontrivial reduction mod 2. "Strengthened" is not compared with that result.
   - Correction: "none of the $2^{21}$ sign lifts passes the 8 sign-point determinant test (a necessary condition for a unit); the unit consequence is implied by Tabei, arXiv:2608.00103." Drop "strengthened".
   - Affects a theorem statement: no for the theorem body (which states the determinant test); yes for the abstract's unit conclusion.
5. **Prior work on the $4 \times 4$ representation.**
   - Where: abstract, lines 72-73; introduction, lines 141-148 ("The unifying mechanism of this paper is the faithful 4-band Bloch representation").
   - What is wrong: the $4 \times 4$ representation of the group ring of $P$ and the determinants of units in it are prior art (Passman, arXiv:2108.06570), not cited. Faithfulness of the evaluation map is not proved in Lean (see the formal issues below).
   - Correction: cite Passman 2021 and Gardam 2023 for the representation and the unit-determinant step; call $\Psi$ the standard $4 \times 4$ representation.
   - Affects a theorem statement: yes (Theorem `thm:t1ab`, faithfulness of $\Psi$, is not kernel-checked as stated).
6. **`T1g`: surjunctivity.**
   - Where: Theorem `thm:t1g`, line 334 ("witnessing Gottschalk surjunctivity on $P$").
   - What is wrong: $P$ is virtually abelian, hence sofic, so surjunctivity on $P$ is already known; the remark adds nothing.
   - Correction: describe `T1g` as the reversible cellular automaton attached to the unit.
   - Affects a theorem statement: no.
7. **`T2b`: gauge classes and the $p = 3$ degeneration.**
   - Where: abstract, lines 84-86; claims table row `T2b`, line 183.
   - What is wrong: the Lean statement is a finite enumeration of a defined discriminant function over 64 sign tuples. The four gauge classes and the 24-code degeneration at $p=3$ are not in the Lean statement; $k_3(8)=24$ is `exact-comp`.
   - Correction: state those parts as computations, not as kernel-checked.
   - Affects a theorem statement: yes (Theorem `thm:t2b` as tagged).
8. **`T2c`: "brand-new" universal no-strings proof.**
   - Where: abstract, lines 87-89; Theorem `thm:t2c`, lines 379-404 (in particular line 404, "Hence Haah's Cubic Code 1 is strictly Type-II ... in every prime qudit dimension"); claims table row `T2c`, line 184.
   - What is wrong: string logical operators are not defined in Lean; the step from the monomial lemma to "no string operators" is on paper only. The Lean hypotheses require roots of three quadratics of discriminant 5, so the statement says nothing over $\mathbb{Z}$, $\mathbb{Q}$ or $\mathbb{F}_p$ with $p \equiv \pm 2 \pmod 5$ without an extension field, and characteristic 2 is covered by one $\mathbb{F}_4$ line only. "Brand-new" is not supported: the qubit property is Haah's (arXiv:1101.1962), and Kim (arXiv:1202.0052) and Dua–Kim–Cheng–Williamson (arXiv:1908.08049) are not cited or compared.
   - Correction: "an algebraic statement that no nontrivial monomial is constant on a rational parametrization of Haah's CC1 curve over integral domains with $2 \neq 0$ containing roots of the three quadratics, plus one $\mathbb{F}_4$ line; the link to string operators is not formalized." Drop "brand-new"; cite Haah 2011, Kim 2012, Dua et al. 2019.
   - Affects a theorem statement: yes (line 404 and the kernel-checked tag of the no-strings conclusion).
9. **`T2d`: code dimensions.**
   - Where: abstract, line 90; Theorem `thm:t2d` items (1) and (3), lines 411-418; claims table row `T2d`, line 185.
   - What is wrong: $k_p(L) \ge 6$, the $6p$ jumps and $k_{23}(11)=6$ are presented within a kernel-checked theorem, but no code-dimension function exists in Lean.
   - Correction: the kernel-checked part is the search showing that $p = 23$ is the first odd prime with an $\mathbb{F}_p$-rational odd-order CC1 point; the $k_p(L)$ values are `exact-comp`.
   - Affects a theorem statement: yes (Theorem `thm:t2d` (1), (3) as tagged).
10. **`T2a`/`T2e`: "first non-Abelian Hantzsche–Wendt fracton codes".**
    - Where: abstract, lines 90-93; subsection title, line 433; Theorem `thm:t2ae`, lines 435-453; claims table rows `T2a`, `T2e`, lines 182, 186.
    - What is wrong: no distance, logical-qubit count or fracton property is formalized; "first" is unsupported (Tian–Samperton–Wang, arXiv:1812.02101; Lin–Pryadko, arXiv:2306.16400, not cited). Line 445, "preserving $k(M_L) = 4 k_{\mathrm{Haah}}(L)$", is not in the Lean statement. Lines 447-448, "Its CSS commutativity is thus an algebraic consequence of Gardam's counterexample", does not follow, because the identity of item (1) also holds for $u = 1$.
    - Correction: "two CSS stabilizer pairs over $\mathbb{F}_2[P]$ / $\mathbb{Z}[P]$"; drop "first" and "fracton"; remove or mark unproven the $k(M_L)$ statement; delete lines 447-448.
    - Affects a theorem statement: yes (Theorem `thm:t2ae` (2)).
11. **`T3a`: Ronkin minimum "strictly" at the origin.**
    - Where: abstract, lines 94-96; Theorem `thm:t3ab` item (1), lines 473-481; claims table row `T3a`, line 187 ("global minimum strictly at $\mu = (0,0,0)$").
    - What is wrong: Lean proves a non-strict inequality for arbitrary midpoint-convex, sign-flip-invariant functions $\mathbb{Q}^3 \to \mathbb{Q}$; the strict version is false (a constant function satisfies the hypotheses). No Ronkin function appears in Lean. The "consequently" bipolar antisymmetry of $W_x$ is a numerical observation.
    - Correction: drop "strictly"; describe `T3a` as an elementary lemma about functions $\mathbb{Q}^3 \to \mathbb{Q}$; mark the Ronkin application as paper-level and the winding symmetry as `numerical-approx`.
    - Affects a theorem statement: yes (table row `T3a`).
12. **`T3b`: "exact quadrilateral characterization" of the double amoeba.**
    - Where: abstract, lines 96-97; Theorem `thm:t3ab` item (2), lines 482-489; claims table row `T3b`, line 188.
    - What is wrong: the "characterization" is the definition of the predicate `InLinearAmoeba` itself, checked at integer radii; no amoeba (image under $\mathrm{Log}|\cdot|$) is defined.
    - Correction: "integer-point checks of defined amoeba inequality predicates, and a nonzero nilpotent $2 \times 2$ matrix".
    - Affects a theorem statement: yes (Theorem `thm:t3ab` (2)).
13. **`T3c`: Artin $B_4$ and monodromy.**
    - Where: abstract, lines 97-100; Theorem `thm:t3c`, lines 518-526; claims table row `T3c`, line 189.
    - What is wrong: no braid group $B_4$ is defined in Lean; the braid relations are checked on permutations in $S_4$, which only shows that the assignment extends to a map $B_4 \to S_4$. That the two permutations are monodromies of $\Psi(\widetilde{\alpha})(k)$ is numerical.
    - Correction: "$S_4$ is generated by two permutations that are observed numerically as monodromies."
    - Affects a theorem statement: yes (the monodromy part of Theorem `thm:t3c` is not kernel-checked).
14. **Verification scope.**
    - Where: abstract, lines 101-104; claims section, line 160.
    - What is wrong: "All 15 exact theorems ... replayed across six independent proof kernels" and "zero sorry" overstate the scope. CI checks the proofs with Lean (`lake build`, `leanchecker`); the 16 comparator targets were also accepted by 6 independent kernels. `lean/PalomarChallenge.lean`, the comparator challenge template, intentionally contains `sorry` bodies.
    - Correction: use the wording above.
    - Affects a theorem statement: no.
15. **Related work.**
    - Where: introduction, lines 114-139; `paper/references.bib`.
    - What is wrong: the following are not cited: Gardam arXiv:2312.05240; Passman arXiv:2108.06570; Tabei arXiv:2608.00103 and arXiv:2609.25015; Kim arXiv:1202.0052; Dua et al. arXiv:1908.08049; Tian–Samperton–Wang arXiv:1812.02101; Lin–Pryadko arXiv:2306.16400.
    - Correction: add these references and position each theorem against them.
    - Affects a theorem statement: no.

### Known issues in the formal code (not yet fixed)

1. **`T1c` first conjunct is a tautology.** Where: `lean/Challenge.lean:46-50`; `lean/PromislowFracton/BlochMatrix.lean:18-28, 136-147`. What is wrong: `TorusPt Int` requires `x * xi = 1`, which forces $x = x_i = \pm 1$, and `TorusPt.v4` only swaps $x \leftrightarrow x_i$, etc., so the action is trivial on integer points. Correction: state $V_4$ invariance for the formal Laurent determinant or over `TorusPt R` for general `R`, and prove "$uv = 1 \Rightarrow$ determinant constant". Affects a theorem statement: yes.
2. **`T1e` is named for a Hensel tower it does not contain.** Where: `lean/Challenge.lean:72-79`; `lean/PromislowFracton/GardamUnit.lean:221-253`. What is wrong: `hensel_geometric_identity` is never applied to `gardamAlpha` / `gardamBeta`. Correction: prove $\widetilde{\alpha}\widetilde{\beta} = 1 - t$ with $t \in 2\mathbb{Z}[P]$ and instantiate the identity, or rename the theorem. Affects a theorem statement: yes (name vs. content).
3. **`T1b` faithfulness is proved for a parallel definition.** Where: `lean/PromislowFracton/BlochMatrix.lean:422-457`. What is wrong: `psiFormal` is not linked to `blochEval`. Correction: prove that each `blochEval` entry is the evaluation of the Laurent polynomial with coefficients `psiFormal`, or define $\Psi$ once. Affects a theorem statement: yes.
4. **Three separate encodings of $\Psi$.** Where: `lean/PromislowFracton/BlochMatrix.lean:549` (`blochAtSign`); `lean/PromislowFracton/GardamUnit.lean` (`zpBlochMat`, `lpDet4`). What is wrong: no lemma links these to `blochEval` or `psiFormal`, so `T1d`, `T1e` and `T1f` concern separately defined matrices. Correction: define $\Psi$ once and derive the sign-point and Laurent forms. Affects a theorem statement: yes (interpretation of `T1d`-`T1f`).
5. **`T1f` lacks the unit step.** Where: `lean/Challenge.lean:82-94`; `lean/PromislowFracton/GardamUnit.lean:460-570`. What is wrong: there is no `det4` multiplicativity lemma, so non-invertibility is not proved. The docstring at `GardamUnit.lean:453` calls the result "BRAND NEW". Correction: add multiplicativity and the evaluation link, or keep the wording "fails the sign-point determinant test"; remove "BRAND NEW". Affects a theorem statement: no (the statement is the determinant test).
6. **`T2c` does not define string operators and is vacuous in many cases.** Where: `lean/Challenge.lean:137-170`; `lean/PromislowFracton/HaahFractons.lean:135-156, 487`. What is wrong: `cc1Px` has no root in $\mathbb{Z}$ (or $\mathbb{Q}$), so Part 1 is vacuous there. Correction: state the string-operator criterion as an explicit hypothesis with a source locator, and state Part 1 for fields containing $\sqrt{5}$. Affects a theorem statement: yes (scope).
7. **Theorem names exceed content.** Where: `lean/Challenge.lean:118-134, 183-229`. What is wrong: names and docstrings of `T2b`, `T2e`, `T3a` (Ronkin), `T3b` (characterization) and `T3c` (Artin $B_4$, monodromy) describe objects not defined in Lean. Correction: rename or reword docstrings. Affects a theorem statement: no (names only).
8. **Wrong roots in a header comment.** Where: `lean/PromislowFracton/NonVacuity.lean:12-13` vs. lines 205-210. What is wrong: the header lists roots `(4, 8, 7)` mod 11; the theorem uses `(2, 4, 3)`, and 4 is not a root of $P_x$ mod 11 (roots: $P_x$ at 2, 6; $P_y$ at 4, 8; $P_z$ at 3, 7). Correction: change the header to `(2, 4, 3)`. Affects a theorem statement: no.
9. **Drafting residue in a docstring.** Where: `lean/PromislowFracton/HaahFractons.lean:750-752`. Correction: rewrite the docstring. Affects a theorem statement: no.
10. **Non-vacuity and adversarial suites do not test statement fidelity.** Where: `lean/PromislowFracton/NonVacuity.lean:14`; `lean/PromislowFracton/AdversarialTests.lean`. What is wrong: the `TorusPt Int` witness is a sign point (which is why `T1c` is trivial), and the only `T2c` witness is `ZMod 11`. Correction: add definition-mutation tests and a characteristic-0 witness containing $\sqrt{5}$. Affects a theorem statement: no.
