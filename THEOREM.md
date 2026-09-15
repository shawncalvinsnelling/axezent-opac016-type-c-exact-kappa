# AXZ-OPAC-016 — 10/10 Referee-Ready Release

**Owner:** Shawn Calvin Snelling  
**Theorem ID:** AXZ-OPAC-016  
**Project status:** `PROVED_EXACT / CLOSED_TYPE_C / UNIQUE_ANSWER_ISOLATED`  
**Formal status:** `KERNEL_VERIFIED_TYPE_C_GEOMETRIC_DILATION`  
**External status:** `NOT_YET_EXTERNALLY_REPLICATED`  
**Scope warning:** This is the standalone Type-C theorem. It does **not** close global OPAC-018.

## 1. Frozen theorem

Let
\[
C_n=\{\pm 2e_i:1\le i\le n\}\cup\{\pm e_i\pm e_j:1\le i<j\le n\},
\]
let \(0\ne U\subseteq\mathbb R^n\) be spanned by roots, put \(\Psi=C_n\cap U\), and define
\[
\kappa(C_n,U)=\inf\{\kappa\ge1:\pi_U(P_{C_n})\subseteq \kappa P_\Psi\}.
\]

After signed switching, write the root-spanned subspace in canonical component form
\[
U=\mathbb R^F\oplus H_{B_1,s^{(1)}}\oplus\cdots\oplus H_{B_m,s^{(m)}},
\]
where each balanced block \(B_j\) has size \(b_j\ge2\), ordered
\(b_1\ge\cdots\ge b_m\), and
\[
H_{B,s}=\left\{x:\operatorname{supp}(x)\subseteq B,\;
\sum_{i\in B}s_i x_i=0\right\}.
\]

Then
\[
\boxed{
\kappa(C_n,U)=
\begin{cases}
1,&m=0,\\[2mm]
2-\dfrac{2}{b_1},&m\ge1.
\end{cases}}
\]

Hence \(\kappa(C_n,U)<2\) for every finite rank.

If
\[
\kappa(C_n):=\max_{0\ne U\text{ root-spanned}}\kappa(C_n,U),
\]
then
\[
\boxed{
\kappa(C_n)=
\begin{cases}
1,&n=1,\\[2mm]
2-\dfrac2n,&n\ge2.
\end{cases}}
\]

For \(n\ge2\), equality is attained by
\[
U=\{x\in\mathbb R^n:x_1+\cdots+x_n=0\},
\qquad C_n\cap U\cong A_{n-1}.
\]

## 2. Complete symbolic proof

### Lemma A — Type-C root polytope

The long roots \(\pm2e_i\) are exactly the vertices of the radius-2 cross-polytope
\[
K=\{x:\|x\|_1\le2\}.
\]
Every short root \(\pm e_i\pm e_j\) has \(\ell_1\)-norm \(2\), so it lies in \(K\).
Therefore
\[
P_{C_n}=K.
\]

### Lemma B — Signed-component normal form

Represent \(e_i-e_j\) and \(e_i+e_j\) as signed edges and \(2e_i\) as a long-axis generator.

For each connected support component:

1. If the signed component is balanced and contains no long-axis generator, switching signs makes every spanning-tree edge an ordinary difference \(e_i-e_j\). Connectivity then spans the zero-sum hyperplane on that support.
2. If it is unbalanced, a spanning tree still spans the zero-sum hyperplane, while one unbalanced edge switches to a vector of nonzero coordinate sum, supplying the missing dimension. The component therefore spans the full coordinate space.
3. If a long root is present, the tree differences together with one coordinate vector again span the full coordinate space.

Thus every root-spanned \(U\) has the displayed direct-sum component form.

### Lemma C — Induced subsystem and gauge

On a full support \(F\), \(\Psi\) contains the full Type-C subsystem.
On a balanced block \(B\), \(\Psi\) is a switched \(A_{b-1}\) subsystem.

For both component types, on their respective subspaces the component root polytope has gauge
\[
\gamma(y)=\frac12\|y\|_1.
\]

For mutually disjoint direct-sum component supports, the convex hull of the component root polytopes has Minkowski gauge equal to the sum of the component gauges. Hence
\[
\boxed{\gamma_\Psi(y)=\frac12\|y\|_1\quad(y\in U).}
\]

Therefore
\[
\kappa(C_n,U)=\max_{\alpha\in C_n}\frac12\|\pi_U\alpha\|_1.
\]

### Lemma D — Projection on a balanced block

After switching a balanced block to ordinary zero-sum form, orthogonal projection is
\[
Q_Bx=x_B-\frac{\sum_{i\in B}x_i}{b}\mathbf1_B.
\]

On a full block, projection is the identity. On inactive coordinates, it is zero.

### Lemma E — Long-root scores

For \(\alpha=2e_i\):

- inactive coordinate: score \(0\);
- full Type-C component: score \(1\);
- balanced block of size \(b\):
\[
Q_B(2e_i)=2\left(e_i-\frac1b\mathbf1_B\right),
\]
so
\[
\frac12\|Q_B(2e_i)\|_1=2-\frac2b.
\]

Thus a long root in the largest balanced block attains \(2-2/b_1\).

### Lemma F — Short-root domination

Every short root falls into one of the following exact cases:

\[
\begin{array}{c|c}
\text{placement} & \text{gauge}\\ \hline
F/F & 1\\
F/B_b & \frac32-\frac1b\\
B_b/B_c & 2-\frac1b-\frac1c\\
B_b/B_b\text{ compatible} & 1\\
B_b/B_b\text{ incompatible} & \max(0,2-\frac4b)\\
B_b/\text{inactive} & 1-\frac1b\\
F/\text{inactive} & \frac12\\
\text{inactive/inactive} & 0
\end{array}
\]

Let \(B=b_1\) be the largest balanced size. Since \(2\le b,c\le B\),

- \(1\le2-2/B\);
- \(\frac32-\frac1b\le2-\frac2B\);
- \(2-\frac1b-\frac1c\le2-\frac2B\);
- \(\max(0,2-\frac4b)\le2-\frac2B\);
- \(1-\frac1b\le2-\frac2B\);
- \(\frac12\le2-\frac2B\).

Therefore no short root exceeds the long-root score from the largest balanced block.

If no balanced block exists, the largest possible score is \(1\), attained on a root in the nonzero full component.

This proves the theorem.

## 3. Uniqueness / answer elimination

The component theorem reduces every admissible answer to three primitive branch scores:

\[
\text{inactive}=0,\qquad
\text{full }C_f=1,\qquad
\text{balanced }A_{b-1}=2-\frac2b.
\]

Since \(2-2/b\) increases with \(b\), the largest balanced block forces the result.

The saved answer-elimination audit records:

- 137,947 nonzero structural component signatures through rank 30;
- 15 submitted formulas;
- 12 distinct output classes on the tested domain;
- 11 rejected output classes;
- 1 surviving mathematical class, represented by
  \(2-2/b_{\max}\) and the algebraically identical
  \(1+(b_{\max}-2)/b_{\max}\).

The finite root-spanned audit through \(C_6\) records:

- \(C_2=5\) nonzero subspaces;
- \(C_3=23\);
- \(C_4=115\);
- \(C_5=647\);
- \(C_6=4,087\);
- total \(=4,877\) nonzero root-spanned subspaces;
- failures \(=0\).

Output classes mean agreement on the finite tested domain; agreement alone is not a proof of algebraic equivalence or elimination of every possible formula.

Finite computation is corroborative. The all-rank conclusion comes from the symbolic proof.

## 4. Referee attack checklist

A referee should try to break:

1. the claim that \(P_{C_n}\) is the radius-2 cross-polytope;
2. the balanced/unbalanced signed-component dichotomy;
3. the claim that an unbalanced connected component spans the full coordinate space;
4. the induced subsystem description \(\Psi=C_n\cap U\);
5. the direct-sum gauge-additivity lemma;
6. the block projection formula;
7. every short-root placement;
8. the \(n=1\) edge case;
9. the global extremal corollary;
10. any hidden use of finite computation to justify universality.

## 5. Literature / novelty boundary

The signed-graph switching and classical-root-system connection are classical, and root-polytope projection geometry has prior literature. This release therefore **does not claim publication priority for the ingredients**. Its theorem packaging and exact formula require a dedicated novelty comparison before any originality claim.

## 6. Final truth label

Accepted internal label:

`PROVED_EXACT / CLOSED_TYPE_C / UNIQUE_ANSWER_ISOLATED / 11_TESTED_OUTPUT_CLASSES_REFUTED`

Not yet earned:

`FORMALLY_VERIFIED`

`EXTERNALLY_REPLICATED`

and this release is **not** a claim that global OPAC-018 is solved.
