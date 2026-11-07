"""Replay the 318/326 contribution without changing its pinned files."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "quartics/quartic-318-326"
WORK = ROOT / "build/quartic-318-326"
WORK.mkdir(parents=True, exist_ok=True)
PACKAGE = Path(tempfile.mkdtemp(prefix="replay-", dir=WORK))
shutil.copytree(SOURCE, PACKAGE, dirs_exist_ok=True, symlinks=True,
                ignore=shutil.ignore_patterns(".lake", ".tooling", ".cache", "__pycache__", "build"))

def run(label, *args):
    print(label, flush=True)
    with (WORK / (label + ".log")).open("w") as log:
        subprocess.run([str(x) for x in args], cwd=PACKAGE, check=True,
                       stdout=log, stderr=subprocess.STDOUT)

run("unpack", sys.executable, "-B", "tools/unpack_data.py")
run("generate", sys.executable, "-B", "tools/generate.py", "--check")
for check in sorted((PACKAGE / "checks").glob("*/*.py")):
    run(check.parent.name + "-" + check.stem, sys.executable, "-B", check)
run("unit-tests", sys.executable, "-B", "-m", "unittest", "discover", "-s", "tests", "-v")
for part, manifest in (("318", "concrete-verification.json"),
                       ("components", "verification.json")):
    base = PACKAGE / "proof" / part
    for name, digest in json.loads((base / manifest).read_text())["sha256"].items():
        assert hashlib.sha256((base / name).read_bytes()).hexdigest() == digest, name
print("PASS: both quartics reproduced; independent finite checks, unit tests, and frozen Lean hashes passed.")
print("Lean was not rebuilt by this command; sourceArithmetic remains an explicit hypothesis.")
