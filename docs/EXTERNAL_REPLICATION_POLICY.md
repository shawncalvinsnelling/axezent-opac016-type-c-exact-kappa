# External Replication Policy

`EXTERNALLY_REPLICATED` is a stronger label than `PROVED_EXACT` and is not earned by informal agreement, AI review, stars, forks, or a passing CI run.

## Minimum requirements

An external replication must:

1. come from a person independent of the project authoring process;
2. identify mathematical competence relevant to finite root systems, Lie/Coxeter combinatorics, convex geometry, or a closely related field;
3. name the exact repository commit SHA reviewed;
4. review the frozen theorem statement and the symbolic all-rank argument, not only finite computation;
5. explicitly address the signed-component normal form, subsystem/gauge step, projection step, extremizer, and short-root case coverage;
6. reproduce at least the fast audit and tests, or explain why independent hand verification makes those computations unnecessary;
7. disclose any suspected prior-art overlap;
8. provide a signed/named report using `REFEREE_REPORT_TEMPLATE.md` or equivalent.

## Promotion rule

Promotion to `EXTERNALLY_REPLICATED` requires at least one qualifying independent report with no unresolved fatal objection. A second independent report is preferred before journal submission.

## Objection rule

A credible counterexample or fatal proof objection immediately blocks promotion and opens an erratum investigation. The historical reviewed commit remains immutable; corrections occur in a new commit/release.
