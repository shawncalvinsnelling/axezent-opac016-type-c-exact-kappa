# Type-C geometric dilation verification

Author: Shawn Calvin Snelling. The formal theorem uses real Euclidean space,
the literal Type-C roots, the literal intersection with a root-spanned subspace,
convex hulls, and Mathlib's orthogonal projection.

For every nonzero root-spanned subspace, the project proves the actual least
admissible dilation, with the original lower cutoff `K >= 1`. It does not
replace the geometric conclusion with assumed component inequalities.

| Statement | Lean theorem |
|---|---|
| Original infimum equals the finite geometric maximum | `geometricKappa_eq_exact` |
| Containment and optimality | `exactGeometricDilation_isLeast` |
| Largest nonfull balanced signed-class size `b >= 2` gives `2 - 2/b` | `exactGeometricDilation_eq_balanced_max` |
| No nontrivial balanced class gives one | `exactGeometricDilation_eq_one_of_no_balanced_block` |
| Every finite-rank value is strictly below two | `exactGeometricDilation_lt_two` |
| Sharp global maximum for `n >= 2` | `rank_bound_isGreatest` |
| Zero-sum hyperplane attains that maximum | `zeroSum_exactGeometricDilation` |
| Sharp rank-one maximum is one | `rank_one_isGreatest` |

The proof obtains signed connected classes from roots actually lying in the
subspace. Nonfull classes are balanced and their coordinate map is injective.
The component normal is orthogonal to the root-spanned subspace. This proves
the genuine projection formula. Explicit averages of induced roots provide
containment certificates; coordinate functionals provide matching lower
bounds. This route proves the dilation theorem without a separate formal
transportation or l1-gauge theorem. The written proof retains that alternative
argument; not every intermediate lemma in that argument is independently
formalized.

## Replay

Lean and Mathlib are pinned to 4.32.1; `lake-manifest.json` locks the exact
dependency revisions.

```sh
cd formal
lake exe cache get
python3 verify.py
```

The gate builds all modules, creates an inventory of every theorem, checks
each transitive axiom report against `propext`, `Classical.choice`, and
`Quot.sound`, and requires a deliberately false theorem to fail. A missing
report or unexpected axiom fails the gate. `verification_receipt.json` records
source hashes, the exact compiler version, and the checked statements. CI
uploads a fresh receipt for the commit it actually checks.

The first complete local verification reused existing workspace proof source
and the pinned compiled Mathlib dependency cache; all project modules were
compiled in an isolated directory. The host required an executable-path
compatibility adapter redirecting `/proc/<own-pid>/exe` to `/proc/self/exe`.
It does not modify Lean, proof terms or the kernel. GitHub runs the standard
toolchain without this adapter.

This is internal mathematical and kernel closure of the standalone Type-C
theorem. Independent replication, institutional acceptance, priority and
global OPAC-018 closure are separate claims.
