# Start review here

For a fast mathematical review:

1. `CLAIMS_AND_NONCLAIMS.md`
2. `THEOREM.md`
3. `docs/DEPENDENCY_MATRIX.md`
4. `docs/REFEREE_CHECKLIST.md`
5. `docs/PRIOR_ART_BOUNDARY.md`

For reproducibility:

```bash
python -m pip install -r requirements-dev.txt
python audit/fast_adversarial_audit.py
python -m pytest -q
```

For the partial Lean arithmetic kernel:

```bash
cd formal
lake update
lake exe cache get
lake build
```

The heavyweight exact `C_2..C_6` enumeration and formula-elimination scripts are provided under `audit/` but are not used as substitutes for the all-rank proof.
