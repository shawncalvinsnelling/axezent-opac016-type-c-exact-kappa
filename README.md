# AXZ-OPAC-016 — Type-C Signed-Component Exact Kappa Lemma

**Author / project owner:** Shawn Calvin Snelling  
**Repository status:** `PROVED_EXACT / CLOSED_TYPE_C / UNIQUE_ANSWER_ISOLATED`  
**Formal status:** `PARTIAL_ARITHMETIC_KERNEL / FULL_GEOMETRY_NOT_YET_FORMALLY_VERIFIED`  
**External status:** `NOT_YET_EXTERNALLY_REPLICATED`

This repository is the standalone home for **AXZ-OPAC-016**. It contains the symbolic all-finite-rank Type-C theorem, adversarial exact-rational audits, the saved answer-elimination evidence, referee documentation, and a Lean arithmetic kernel.

> **Scope boundary:** this repository does **not** claim that global OPAC-018 is solved.

## Frozen result

For every finite Type-`C_n` root system and every nonzero root-spanned subspace `U`, let `b_max` be the largest balanced signed-component size. Then

```text
kappa(C_n,U) = 1                     if there is no balanced component,
kappa(C_n,U) = 2 - 2/b_max           otherwise.
```

Consequently `kappa(C_n,U) < 2` for every finite rank. If `kappa(C_n)` denotes the maximum over nonzero root-spanned `U`, then

```text
kappa(C_1) = 1,
kappa(C_n) = 2 - 2/n                 for n >= 2,
```

with the `n >= 2` maximum attained by the zero-sum `A_{n-1}` hyperplane.

## Start here

1. [`START_REVIEW_HERE.md`](START_REVIEW_HERE.md) — referee entry point.
2. [`THEOREM.md`](THEOREM.md) — frozen theorem and symbolic proof.
3. [`CLAIMS_AND_NONCLAIMS.md`](CLAIMS_AND_NONCLAIMS.md) — truth boundary.
4. [`docs/REFEREE_RELEASE.md`](docs/REFEREE_RELEASE.md) — compact referee release.
5. [`docs/DEPENDENCY_MATRIX.md`](docs/DEPENDENCY_MATRIX.md) — proof dependency ledger.
6. [`docs/REFEREE_CHECKLIST.md`](docs/REFEREE_CHECKLIST.md) — hostile-referee checklist.
7. [`REFEREE_REPORT_TEMPLATE.md`](REFEREE_REPORT_TEMPLATE.md) — independent review report form.
8. [`docs/EXTERNAL_REPLICATION_POLICY.md`](docs/EXTERNAL_REPLICATION_POLICY.md) — requirements for `EXTERNALLY_REPLICATED`.
9. [`docs/LITERATURE_COMPARISON.md`](docs/LITERATURE_COMPARISON.md) — prior-art comparison and priority boundary.
10. [`ERRATA.md`](ERRATA.md) and [`CHANGELOG.md`](CHANGELOG.md) — permanent correction/change ledger.

## Reproduce the fast audit

The referee CI pins Python 3.11, SymPy, and pytest via `constraints.txt`.

```bash
python -m pip install -c constraints.txt -r requirements-dev.txt
python audit/fast_adversarial_audit.py
python -m pytest -q
```

The full `C_2..C_6` subspace enumeration is intentionally separate because it is much heavier. It can be run manually or from the **OPAC-016 Heavy Exact Audit** GitHub Action:

```bash
python audit/exact_subspace_audit.py
python audit/formula_elimination.py
```

## Evidence already recorded

- 4,877 exact root-spanned subspaces through `C_6` in the saved full audit.
- 137,947 nonzero component-size signatures through rank 30 (zero subspaces excluded).
- 15 submitted formulas -> 12 distinct output classes on the tested domain -> 11 rejected -> 1 surviving tested class.
- 269,902 exact scalar adversarial checks in the fast audit, with zero failures.
- Lean arithmetic kernel source with a no-`sorry` / no-project-axiom CI gate.

Output classes mean agreement on the finite tested domain; agreement alone is not a proof of algebraic equivalence or elimination of every possible formula.

Finite computation is corroborative. The universal statement is supported by the symbolic proof in `THEOREM.md`.

## External review governance

- Every referee report must name the exact commit SHA reviewed.
- Mathematical objections, candidate counterexamples, reproducibility failures, prior-art reports, and Lean issues each have a dedicated GitHub issue form.
- `EXTERNALLY_REPLICATED` is reserved for a qualifying independent mathematical review under `docs/EXTERNAL_REPLICATION_POLICY.md`.
- Reviewed commits are never silently rewritten; corrections go into `ERRATA.md`, `CHANGELOG.md`, and a new version.
- `docs/RELEASE_CHECKLIST.md` defines the archival release/DOI handoff.
- `docs/AI_ASSISTANCE_DISCLOSURE.md` records AI and computational assistance transparently.

## Truth boundary

Safe project label:

`PROVED_EXACT / CLOSED_TYPE_C / UNIQUE_ANSWER_ISOLATED / 11_TESTED_OUTPUT_CLASSES_REFUTED`

Not yet claimed:

- `FORMALLY_VERIFIED` for the complete geometric theorem;
- `EXTERNALLY_REPLICATED` by an independent mathematician;
- journal acceptance;
- publication priority/novelty;
- closure of global OPAC-018.
