# Formal verification

Current formal status: **partial arithmetic kernel verified / full geometry not yet kernel-checked**.

`OPAC016Arithmetic.lean` formalizes the scalar inequalities used after the geometric signed-component theorem is established. It does not yet formalize the complete root-system classification, induced subsystem geometry, Minkowski-gauge argument, or orthogonal projection construction.

The repository must not be labeled `FORMALLY_VERIFIED` until the complete proof compiles without `sorry` or project-specific axioms and receives independent review.

## Remaining geometry obligations

`global_bound` proves only monotonicity of the real-valued expression `balancedScore`. It does not define or identify geometric kappa. Additional scalar inequalities alone cannot close this gap.

The complete formal dependency chain still needs:

1. A Type-C root set and proof that its convex hull is the radius-2 l1 ball.
2. The signed-component decomposition of every nonzero root-spanned subspace, including inactive coordinates.
3. Identification of the induced subsystem and its gauge as half the l1 norm on that subspace.
4. The orthogonal projector on balanced blocks, and the projected long-root score.
5. Convexity to bound projected short roots by projected long roots.
6. Assembly of the kappa formula, then the dimension bound and equality witness for the zero-sum hyperplane; handle n=1 separately.

No formal theorem in this repair claims these obligations have been discharged.
