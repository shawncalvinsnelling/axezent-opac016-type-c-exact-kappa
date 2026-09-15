import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("fast", ROOT / "audit" / "fast_adversarial_audit.py")
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

def test_fast_exact_audit_passes():
    data = mod.run()
    assert data["status"] == "PASS"
    assert data["failures"] == []
    assert data["checks"] >= 250_000
