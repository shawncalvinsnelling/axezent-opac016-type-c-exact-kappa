# Review Version and Immutability Policy

External review is always tied to an exact Git commit SHA and, when available, a tagged GitHub release.

- Never describe a moving `main` branch as the object that was reviewed.
- Never silently rewrite a reviewed proof to erase an objection.
- Corrections are committed openly and recorded in `ERRATA.md` and `CHANGELOG.md`.
- A material theorem/proof correction requires a new release/version and a fresh referee check of the changed dependency chain.
- Computational receipts must identify the program version/commit that generated them.
- The truth label may be downgraded if a defect affects a proved dependency.

Recommended first archival release: `v1.0.0-referee` after the governance CI is green. If Zenodo is connected to the GitHub repository, archive that release to obtain an immutable DOI snapshot.
