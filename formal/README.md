# Formal verification

Current formal status: **partial arithmetic kernel verified / full geometry not yet kernel-checked**.

`OPAC016Arithmetic.lean` formalizes the scalar inequalities used after the geometric signed-component theorem is established. It does not yet formalize the complete root-system classification, induced subsystem geometry, Minkowski-gauge argument, or orthogonal projection construction.

The repository must not be labeled `FORMALLY_VERIFIED` until the complete proof compiles without `sorry` or project-specific axioms and receives independent review.
