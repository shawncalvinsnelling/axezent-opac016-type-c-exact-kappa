# Start review here

Review **one exact commit SHA**, not a moving branch.

## Mathematical review order

1. `CLAIMS_AND_NONCLAIMS.md`
2. `THEOREM.md`
3. `docs/DEPENDENCY_MATRIX.md`
4. `docs/REFEREE_CHECKLIST.md`
5. `docs/LITERATURE_COMPARISON.md`
6. `docs/PRIOR_ART_BOUNDARY.md`
7. `REFEREE_REPORT_TEMPLATE.md`
8. `docs/EXTERNAL_REPLICATION_POLICY.md`

## Fast reproducibility

```bash
python -m pip install -c constraints.txt -r requirements-dev.txt
python audit/fast_adversarial_audit.py
python -m pytest -q
```

## Heavy reproducibility

Use **Actions -> OPAC-016 Heavy Exact Audit -> Run workflow** for an environment-recorded replay of the exact `C_2..C_6` enumeration and formula elimination. The workflow uploads logs, versions, commit SHA, and SHA-256 receipts.

Manual equivalent:

```bash
python audit/exact_subspace_audit.py
python audit/formula_elimination.py
```

## Partial Lean arithmetic kernel

```bash
cd formal
lake update
lake exe cache get
lake build
```

The Lean CI rejects `sorry` and project-defined `axiom` declarations in the arithmetic kernel. The complete signed-graph/root-polytope/projection geometry is **not yet fully encoded in Lean**.

## How to report findings

Use the repository issue forms for:

- mathematical proof review;
- candidate counterexamples;
- reproducibility failures;
- prior-art/literature overlap;
- Lean formalization issues.

For a completed independent review, use `REFEREE_REPORT_TEMPLATE.md`, name the exact commit SHA, and follow `docs/EXTERNAL_REPLICATION_POLICY.md`.

Reviewed commits are immutable review objects. Corrections are recorded openly in `ERRATA.md` and `CHANGELOG.md` and require a new version/review where material.
