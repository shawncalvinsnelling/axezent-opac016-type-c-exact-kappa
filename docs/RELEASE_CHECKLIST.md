# Referee Release Checklist

Before publishing an archival referee release:

- [ ] `THEOREM.md` statement is frozen and includes the `C_1` exception.
- [ ] `CLAIMS_AND_NONCLAIMS.md` still excludes global OPAC-018 closure.
- [ ] Fast exact-audit CI is green at the release commit.
- [ ] Lean complete-geometry verification CI is green at the release commit.
- [ ] Heavy exact audit has been run at least once for the release commit or its omission is documented.
- [ ] `constraints.txt` and Lean toolchain are pinned.
- [ ] `CITATION.cff` matches author, repository, version, and release date.
- [ ] `ERRATA.md` and `CHANGELOG.md` are current.
- [ ] `docs/LITERATURE_COMPARISON.md` is current.
- [ ] AI/computational assistance disclosure is included.
- [ ] SHA/commit of the reviewed object is recorded in any outgoing referee request.
- [ ] GitHub release/tag is created from the reviewed commit.
- [ ] Optional: archive the release with Zenodo and record the DOI here.

**Release commit:**  
**GitHub tag:**  
**DOI (if any):**  
