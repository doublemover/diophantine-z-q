"""Replay the 318/326 contribution without changing its pinned files."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from check_quartic_consumer_bindings import verify as verify_consumers

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "quartics/quartic-318-326"
WORK = ROOT / "build/quartic-318-326"
WORK.mkdir(parents=True, exist_ok=True)
PACKAGE = Path(tempfile.mkdtemp(prefix="replay-", dir=WORK))
shutil.copytree(SOURCE, PACKAGE, dirs_exist_ok=True, symlinks=True,
                ignore=shutil.ignore_patterns(".lake", ".tooling", ".cache", "__pycache__", "build"))

def run(label, *args):
    print(label, flush=True)
    log_path = WORK / (label + ".log")
    try:
        with log_path.open("w") as log:
            subprocess.run([str(x) for x in args], cwd=PACKAGE, check=True,
                           stdout=log, stderr=subprocess.STDOUT)
    except subprocess.CalledProcessError:
        print(f"FAILED {label}; exact child output follows:", file=sys.stderr, flush=True)
        print(log_path.read_text(), file=sys.stderr, flush=True)
        raise

run("unpack", sys.executable, "-B", "tools/unpack_data.py")
run("generate", sys.executable, "-B", "tools/generate.py", "--check")
for check in sorted((PACKAGE / "checks").glob("*/*.py")):
    run(check.parent.name + "-" + check.stem, sys.executable, "-B", check)
run("unit-tests", sys.executable, "-B", "-m", "unittest", "discover", "-s", "tests", "-v")
run("integration-regressions", sys.executable, "-B", ROOT / "scripts/test_quartic_integration.py")
# Use the repository's shared source policy, but validate the copied package bytes.
run("progress-manifest", sys.executable, "-B", SOURCE / "proof/progress/verify_manifest.py",
    "--root", PACKAGE / "proof/progress")
historical_obligations = verify_consumers(ROOT)
for part, manifest in (("318", "concrete-verification.json"),
                       ("components", "verification.json")):
    base = PACKAGE / "proof" / part
    for name, digest in json.loads((base / manifest).read_text())["sha256"].items():
        bound = historical_obligations if (part, name) == ("components", "arithmetic-obligations.md") else base / name
        assert hashlib.sha256(bound.read_bytes()).hexdigest() == digest, name
receipt_dir = PACKAGE / "proof/receipts/fresh-rebuild"
for name, digest in json.loads((receipt_dir / "receipt.json").read_text())["sha256"].items():
    assert hashlib.sha256((receipt_dir / name).read_bytes()).hexdigest() == digest, name
source_check = json.loads((receipt_dir / "source-check.json").read_text())
for part in ("318", "components"):
    assert hashlib.sha256((receipt_dir / (part + "-manifest.json")).read_bytes()).hexdigest() == source_check["packages"][part]["manifestSHA256"]
print("PASS: fresh Lean rebuild evidence and added proof-source hashes match.")
print("PASS: both quartics reproduced; independent finite checks, unit tests, and frozen Lean hashes passed.")
print("PASS: progress snapshot source hashes, closed imports, build order, and placeholder checks. This is not a Lean replay.")
print("Lean was not rebuilt by this command; sourceArithmetic remains an explicit hypothesis.")
