"""Compile the complete Type-C theorem and fail closed on unexpected axioms."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def run(args, expected_success=True):
    result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True)
    output = result.stdout + result.stderr
    print(output, end="", flush=True)
    if expected_success and result.returncode:
        raise SystemExit(result.returncode)
    return result, output


def main():
    files = sorted(ROOT.glob("OPAC016*.lean"))
    names = []
    for path in files:
        source = path.read_text()
        if re.search(r"\b(?:sorry|admit|unsafe|implemented_by|native_decide)\b|^\s*axiom\b",
                     source, re.M):
            raise SystemExit("Forbidden proof escape or placeholder: " + path.name)
        names.extend("OPAC016." + name for name in re.findall(
            r"^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+(\w+)", source, re.M))
    if not names or len(names) != len(set(names)):
        raise SystemExit("Missing or duplicate theorem inventory")
    probe = ROOT / "AllAxioms.lean"
    probe.write_text("\n".join(["import " + p.stem for p in files]
                              + ["#print axioms " + name for name in names]) + "\n")
    run(["lake", "build"])
    _, output = run(["lake", "env", "lean", probe.name])
    audit = {}
    for name in names:
        match = re.search(re.escape(name) + r"' depends on axioms: \[(.*?)\]",
                          output, re.S)
        if match:
            axioms = {x.strip() for x in match.group(1).split(",") if x.strip()}
        elif re.search(re.escape(name) + r"' does not depend on any axioms", output):
            axioms = set()
        else:
            raise SystemExit("Missing axiom report: " + name)
        if axioms - ALLOWED:
            raise SystemExit("Unexpected axioms: " + name + repr(axioms - ALLOWED))
        audit[name] = sorted(axioms)
    control = ROOT / "FalseControl.lean"
    control.write_text("import OPAC016SharpRank\ntheorem false_control : False := by trivial\n")
    result, output = run(["lake", "env", "lean", control.name], expected_success=False)
    if result.returncode == 0 or "⊢ False" not in output or "error: Tactic" not in output:
        raise SystemExit("False-theorem control was not rejected as expected")
    _, version = run(["lake", "env", "lean", "--version"])
    tracked = files + [ROOT / p for p in ["lakefile.lean", "lean-toolchain",
                                        "lake-manifest.json", "verify.py"]]
    receipt = {
        "status": "PASS",
        "scope": "TYPE_C_ACTUAL_LEAST_GEOMETRIC_DILATION_BALANCED_MAX_AND_SHARP_RANK",
        "author": "Shawn Calvin Snelling",
        "lean": version.strip(),
        "theorem_count": len(audit),
        "axioms": audit,
        "source_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in tracked},
        "false_control_rejected": True,
        "external_review_claimed": False,
    }
    (ROOT / "verification_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: v for k, v in receipt.items() if k not in {"axioms", "source_sha256"}}, indent=2))


if __name__ == "__main__":
    main()
