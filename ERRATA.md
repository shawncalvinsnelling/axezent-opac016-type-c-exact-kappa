# Errata

This file is the permanent public correction ledger for AXZ-OPAC-016.

## Current status

No accepted mathematical errata are recorded as of the initial standalone referee package.

## Required format for future entries

### ERR-YYYY-NNN — short title

- **Reported:**
- **Affected commit/release:**
- **Affected theorem/lemma:**
- **Severity:** clarification / local correction / truth-label affecting
- **Description:**
- **Resolution commit:**
- **Truth-label impact:**
- **Independent confirmation:**

Historical reviewed commits are never rewritten; corrections are additive and versioned.

## ERR-2026-001 — formula audit arity and stale evidence counts

- Reported: 2026-09-15.
- Affected commit: d51beeb37a7749f26fa24555b6e8fca78c7491d9 and its inherited audit source/receipt.
- Severity: reproducibility correction and bounded-evidence clarification; no theorem change.
- The rational helper accepted one argument although candidates supplied numerator and denominator. Corrected to accept both, with denominator defaulting to one.
- The source has 15 submitted formulas, not the receipt's 18. A fresh exact C2-C6 run yields 12 tested output classes, 11 rejected classes, and one surviving tested class containing the target and its algebraic rewrite.
- The old 137,976 signature count included 29 zero-subspace signatures. The corrected theorem-domain count is 137,947 nonzero signatures through rank 30.
- Added import-safe execution, bounded CLI controls, deterministic ordering, counterexamples for every rejected output class, source hashes, and a regular-CI regression exercising all candidates.
- Regenerated the canonical receipt from the repaired executable; the prior evidence remains available in Git history.
- Resolution: the commit introducing this entry and repaired audit, identifiable through Git history.
- Truth-label impact: the written Type-C formula is unchanged. Full geometric formal verification, external replication, and novelty remain unestablished.
- Independent confirmation: no external referee confirmation claimed. Local exact replay and regression results are recorded in the repair documentation.
