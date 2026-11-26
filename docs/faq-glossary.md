<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# FAQ & Glossary (`docs/faq-glossary.md`)

## Glossary
- **Promislow / Hantzsche–Wendt Group ($P$):** The unique torsion-free $3$-dimensional crystallographic group with finite abelianization ($\Z_4^2$), fundamental group of the flat Hantzsche–Wendt $3$-manifold, presented by $\langle a,b \mid a^{-1}b^2a = b^{-2},\, b^{-1}a^2b = a^{-2}\rangle$ with index-$4$ normal translation lattice $N \cong \Z^3$ and quotient $V_4$.
- **Bloch Representation ($\Psi$):** The standard $4 \times 4$ matrix representation $\Psi : R[P] \to M_4(R[x^{\pm 1}, y^{\pm 1}, z^{\pm 1}])$ obtained from the action of $R[P]$ on the 4 cosets of $N$ (see Passman, arXiv:2108.06570). In Lean, the evaluation map is shown to preserve $1$, $+$ and $\times$; injectivity is proved only for a separate coefficient map.
- **Gardam Unit ($\alpha, \beta$):** Giles Gardam's 2021 21-term nontrivial unit in $\F_2[P]$ disproving Kaplansky's Unit Conjecture in characteristic $2$. Gardam later showed that $\mathbb{C}[P]$ also has non-trivial units (arXiv:2312.05240).
- **Type-II Fracton Code:** A $3$D local stabilizer quantum code (exemplified by Haah's Cubic Code 1) whose point-like topological excitations are completely immobile and admit no mobile $1$D string logical operators.
- **Amoeba ($\mathcal{A}(f)$) & Ronkin Function ($R(\mu)$):** The log-modulus projection $\mathcal{A}(f) = \{\log|z| : f(z) = 0\} \subset \R^d$ and its convex potential $R(\mu) = \int_{\T^d} \log|f(e^{\mu+ik})|\,\frac{d^dk}{(2\pi)^d}$, governing multi-dimensional non-Hermitian skin decay rates.
- **Canonical Quartic Discriminant Braid Degree ($\deg_\Delta$):** The coordinate-free integer winding number $\frac{1}{2\pi}\oint_\gamma d\arg \Disc(\det(\lambda I_4 - H(k)))$ measuring non-Hermitian $B_4$ band braiding without projection-angle ambiguity.

## Frequently Asked Questions
**Q1: Does this paper solve Kaplansky's Unit Conjecture in characteristic 0?**
No. Over $\mathbb{C}$ the conjecture is already false (Gardam, arXiv:2312.05240, for this group $P$). Whether $\Z[P]$ or $\mathbb{Q}[P]$ has non-trivial units remains open. Theorem `T1f` shows that none of the $2^{21}$ sign lifts on Gardam's support passes the 8 sign-point determinant test, a necessary condition for a unit; Lean does not prove that they are non-units, and that conclusion is implied by Tabei, arXiv:2608.00103. Invertibility of $\widetilde{\alpha}$ in $(\Z/2^m\Z)[P]$ is standard lifting and is not formalized for Gardam's unit (`LIMITATIONS.md`).

**Q2: Why zero Mathlib?**
Zero Mathlib keeps the trusted proof-checking base small and avoids version drift. CI checks the proofs with Lean (`lake build`, `leanchecker`); the 16 comparator targets were also accepted by 6 independent kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`).

**Q3: How do I launch the 3D WebGL2 studio offline?**
Simply open `studio/index.html` or `blueprint/index.html` in any modern WebGL2-capable browser—both are single-file, zero-dependency HTML/JS applications requiring no build step or internet access.
