"""Exercise the audit that the fast scalar suite previously missed."""
import importlib.util
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('formula', ROOT/'audit/formula_elimination.py')
formula = importlib.util.module_from_spec(spec)
spec.loader.exec_module(formula)


def test_formula_cli_and_generated_evidence(tmp_path):
    output=tmp_path/'receipt.json'
    subprocess.run([sys.executable,str(ROOT/'audit/formula_elimination.py'),
                    '--max-rank','3','--signature-rank','6','--output',str(output)],
                   cwd=tmp_path,check=True,capture_output=True,text=True)
    receipt=json.loads(output.read_text())
    assert receipt['exact_root_spanned_subspaces_tested']==28
    assert receipt['candidate_formulas_submitted']==len(formula.candidates)==15
    assert receipt['status']=='PASS'
    assert all(c['first_counterexample'] is not None
               for c in receipt['all_output_classes'] if not c['survives'])
    assert any('K2_2-2/b1 [TARGET]' in c['names'] for c in receipt['surviving_output_classes'])


def test_zero_subspace_excluded_from_signature_domain():
    signatures=formula.component_signatures(6)
    assert signatures
    assert all(f or bs for _,f,bs,_ in signatures)


def test_target_failure_is_not_reported_as_pass(monkeypatch):
    import pytest
    monkeypatch.setitem(formula.candidates,'K2_2-2/b1 [TARGET]',lambda d: formula.Q(99))
    with pytest.raises(RuntimeError,match='Target audit failed'):
        formula.run(2,2)


def test_canonical_receipt_matches_audited_sources():
    import hashlib
    receipt=json.loads((ROOT/'receipts/formula_elimination_receipt.json').read_text())
    assert receipt['candidate_names']==list(formula.candidates)
    assert receipt['candidate_formulas_submitted']==len(formula.candidates)
    assert receipt['distinct_output_classes_on_tested_domain']==len(receipt['all_output_classes'])
    for name,expected in receipt['source_sha256'].items():
        assert hashlib.sha256((ROOT/'audit'/name).read_bytes()).hexdigest()==expected
