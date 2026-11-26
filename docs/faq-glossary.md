<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# FAQ & Glossary (`docs/faq-glossary.md`)

## Glossary
- **Promislow / Hantzsche–Wendt Group ($P$):** The unique torsion-free $3$-dimensional crystallographic group with finite abelianization ($\Z_4^2$), fundamental group of the flat Hantzsche–Wendt $3$-manifold, presented by $\langle a,b \mid a^{-1}b^2a = b^{-2},\, b^{-1}a^2b = a^{-2}\rangle$ with index-$4$ normal translation lattice $N \cong \Z^3$ and quotient $V_4$.
- **Bloch Embedding ($\Psi$):** The faithful $4 \times 4$ matrix representation $\Psi : R[P] \hookrightarrow M_4(R[x^{\pm 1}, y^{\pm 1}, z^{\pm 1}])$ obtained from the left regular action of $R[P]$ on its 4 cosets of $N$.
- **Gardam Unit ($\alpha, \beta$):** Giles Gardam's 2021 21-term nontrivial unit in $\F_2[P]$ disproving Kaplansky's Unit Conjecture in characteristic $2$.
- **Type-II Fracton Code:** A $3$D local stabilizer quantum code (exemplified by Haah's Cubic Code 1) whose point-like topological excitations are completely immobile and admit no mobile $1$D string logical operators.
- **Amoeba ($\mathcal{A}(f)$) & Ronkin Function ($R(\mu)$):** The log-modulus projection $\mathcal{A}(f) = \{\log|z| : f(z) = 0\} \subset \R^d$ and its convex potential $R(\mu) = \int_{\T^d} \log|f(e^{\mu+ik})|\,\frac{d^dk}{(2\pi)^d}$, governing multi-dimensional non-Hermitian skin decay rates.
- **Canonical Quartic Discriminant Braid Degree ($\deg_\Delta$):** The coordinate-free integer winding number $\frac{1}{2\pi}\oint_\gamma d\arg \Disc(\det(\lambda I_4 - H(k)))$ measuring non-Hermitian $B_4$ band braiding without projection-angle ambiguity.

## Frequently Asked Questions
**Q1: Does this paper solve Kaplansky's Unit Conjecture in characteristic 0?**
No. Theorem `T1f` rules out all $2^{21}$ sign lifts on Gardam's support (and arbitrary even-sum $p \in \Z[N]$ paired with Gardam's 13-element $(q,r,s)$ support) in $\Z[P]$, while `T1e` shows $\widetilde{\alpha}$ lifts $2$-adically to $(\Z/2^m\Z)[P]^\times$ for every finite $m \ge 1$. General characteristic-$0$ supports remain explicitly OPEN (`LIMITATIONS.md`).

**Q2: Why zero Mathlib?**
Zero Mathlib keeps the trusted proof-checking base tiny, allows all 6 independent kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`) to replay the entire formalization in seconds, and guarantees clean-room reproducibility without version drift.

**Q3: How do I launch the 3D WebGL2 studio offline?**
Simply open `studio/index.html` or `blueprint/index.html` in any modern WebGL2-capable browser—both are single-file, zero-dependency HTML/JS applications requiring no build step or internet access.
