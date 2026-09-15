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

1. [`THEOREM.md`](THEOREM.md) — frozen theorem and symbolic proof.
2. [`docs/REFEREE_RELEASE.md`](docs/REFEREE_RELEASE.md) — compact 10/10 referee release.
3. [`docs/DEPENDENCY_MATRIX.md`](docs/DEPENDENCY_MATRIX.md) — proof dependency ledger.
4. [`docs/REFEREE_CHECKLIST.md`](docs/REFEREE_CHECKLIST.md) — hostile-referee checklist.
5. [`docs/PRIOR_ART_BOUNDARY.md`](docs/PRIOR_ART_BOUNDARY.md) — novelty and literature boundary.
6. [`audit/`](audit/) — exact-rational verification programs.
7. [`receipts/`](receipts/) — machine-readable evidence.
8. [`formal/`](formal/) — Lean arithmetic kernel and formalization boundary.

## Reproduce the fast audit

```bash
python -m pip install -r requirements-dev.txt
python audit/fast_adversarial_audit.py
python -m pytest -q
```

The full `C_2..C_6` subspace enumeration is intentionally separate because it is much heavier:

```bash
python audit/exact_subspace_audit.py
python audit/formula_elimination.py
```

## Evidence already recorded

- 4,877 exact root-spanned subspaces through `C_6` in the saved full audit.
- 137,976 component-size signatures through rank 30.
- 18 proposed formulas -> 15 distinct answer classes -> 14 eliminated -> 1 mathematical answer class.
- 269,902 exact scalar adversarial checks in the fast 10/10 audit, with zero failures.
- Lean arithmetic kernel source with a no-`sorry` / no-project-axiom CI gate.

Finite computation is corroborative. The universal statement is supported by the symbolic proof in `THEOREM.md`.

## Truth boundary

Safe project label:

`PROVED_EXACT / CLOSED_TYPE_C / UNIQUE_ANSWER_ISOLATED / 14_ALTERNATIVE_CLASSES_REFUTED`

Not yet claimed:

- `FORMALLY_VERIFIED` for the complete geometric theorem;
- `EXTERNALLY_REPLICATED` by an independent mathematician;
- journal acceptance;
- publication priority/novelty;
- closure of global OPAC-018.
