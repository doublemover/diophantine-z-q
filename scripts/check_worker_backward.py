"""Check exact, dependency-closed worker drafts without a project artifact cache."""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_progress_lean as ci
from check_progress_experiment import audit_text

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("mode", choices=["targets", "check"])
parser.add_argument("packet", choices=["witness", "arithmetic", "integration", "finite", "signed", "same-j-upper-abel-jets-r1", "same-j-upper-diagonal-probe-r1", "same-j-upper-field-pic-r1", "same-j-upper-haar-r1", "same-j-upper-relative-test-probe-r1", "same-j-upper-verified-core-r1"])
args = parser.parse_args()
source = ROOT / "quartics/quartic-318-326/proof/intake/worker-backward-20261125" / args.packet
order = json.loads((source / "kernel.json").read_bytes())
assert isinstance(order, dict) and order
seen, official = set(), set()
for name, digest in order.items():
    assert re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", name), name
    f = source / (name + ".lean")
    assert f.is_file() and not f.is_symlink()
    b = f.read_bytes()
    assert hashlib.sha256(b).hexdigest() == digest, name
    for dep in ci.import_names(b.decode("utf-8")):
        if dep.startswith("Mathlib.") or dep.startswith("Lean.") or dep.startswith("Init."):
            if dep.startswith("Mathlib."):
                official.add(dep)
        elif dep not in seen:
            raise ValueError(f"{name}: missing or unordered local import {dep}")
    seen.add(name)
if args.mode == "targets":
    print(*sorted(official), sep="\n")
    sys.exit(0)
out = ROOT / "build/worker-backward" / args.packet
out.mkdir(parents=True, exist_ok=False)
lib = out / "lib"
lib.mkdir()
env, version = ci.environment(ci.PROJECT, lib)
report = {"toolchain": version, "sources": order, "checks": [], "status": "failed",
          "scope": "Draft source compilation and recursive axiom audit only; no endpoint acceptance"}
try:
    for name in order:
        report["checks"].append(ci.compile_one(ci.PROJECT, env, name, source / (name + ".lean"),
                                               lib / (name + ".olean"), out / "logs", root=source))
    audit = out / "WorkerAudit.lean"
    audit.write_text(audit_text(list(order)), encoding="utf-8")
    ci.compile_one(ci.PROJECT, env, "WorkerAudit", audit, None, out / "logs", root=out)
    log = (out / "logs/WorkerAudit.log").read_text(encoding="utf-8")
    match = re.search(r"EXPERIMENT_AUDIT_PASS declarations=([1-9][0-9]*) modules=([1-9][0-9]*)", log)
    if not match or int(match[2]) != len(order):
        raise RuntimeError("Missing or incomplete recursive audit")
    report.update(status="passed", audited_declarations=int(match[1]))
except Exception as e:
    report["error"] = str(e)
    for path in sorted((out / "logs").glob("*.log")):
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
        hits = [i for i, line in enumerate(lines) if "error:" in line or "error(" in line]
        if hits:
            print(f"{path.name}: first Lean failure")
            print("\n".join(lines[hits[0]:hits[0]+22]))
    raise
finally:
    (out / "RESULT.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
