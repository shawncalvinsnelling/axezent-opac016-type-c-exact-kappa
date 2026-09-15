# Formula audit repair — 2026-09-15

Prepared for Shawn Calvin Snelling.

Base reviewed: d51beeb37a7749f26fa24555b6e8fca78c7491d9.

The unmodified source defined `Q(x)` but invoked two-argument rational construction. The corrected `Q(numerator, denominator=1)` accepts every existing candidate. The module is now safe to import without starting an expensive run.

Executed locally with Python 3.12.14 and SymPy 1.14.0:

```sh
python3 audit/formula_elimination.py --output receipts/formula_elimination_receipt.json
python3 -m pytest -q
```

The receipt records the actual Python version and SHA-256 hashes of both mathematical audit sources. The exact run completed C2-C6, totaling 4,877 nonzero subspaces. It evaluated 15 candidate formulas, found 12 distinct output vectors, rejected 11, and retained the target with its algebraic rewrite. It also checked 137,947 nonzero component signatures through rank 30. The discarded 29 zero signatures were outside the theorem's domain.

All five regression tests passed, including the fast scalar audit, the formula CLI on C2-C3, a deliberately corrupted target, zero-subspace exclusion, and canonical receipt/source binding. The formula CLI test executes every candidate and is automatically included in the existing CI pytest step.

The component-signature calculation compares scalar branch expressions; it is not independent verification of all geometric subspaces through rank 30. The exact subspace calculation uses rational projectors and the written gauge identification. Agreement on a finite domain does not establish algebraic equivalence between arbitrary candidate functions or rule out all imaginable formulas.

The theorem is unchanged. Lean still verifies only the arithmetic kernel. The remaining geometry obligations are listed in `formal/README.md`. No external review, publication novelty, full formal verification, or global OPAC-018 closure is claimed.
