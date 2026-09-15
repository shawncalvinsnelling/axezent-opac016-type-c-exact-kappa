# Reproducibility Environment

## Fast exact audit

Canonical CI environment:

- OS: GitHub Actions `ubuntu-latest`
- Python: `3.11`
- SymPy: `1.14.0`
- pytest: `9.0.2`

Install with:

```bash
python -m pip install -c constraints.txt -r requirements-dev.txt
```

Then run:

```bash
python audit/fast_adversarial_audit.py
python -m pytest -q
```

## Heavy exact audit

Use the manual GitHub Action **OPAC-016 Heavy Exact Audit**. It records the commit SHA, OS/kernel information, Python/package versions, logs, and SHA-256 hashes as a downloadable workflow artifact.

## Lean

The Lean toolchain and Mathlib revision are controlled by `formal/lean-toolchain` and `formal/lakefile.lean`. CI rejects `sorry` and project-defined `axiom` declarations in the arithmetic kernel.

Environment pinning improves reproducibility; it does not substitute for the symbolic proof.
