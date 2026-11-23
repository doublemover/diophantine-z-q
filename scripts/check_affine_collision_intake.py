#!/usr/bin/env python3
"""Hosted-only affine collision intake: three fresh modules, no project cache."""

import argparse
from contextlib import contextmanager
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

import check_progress_experiment as experiment
import check_progress_lean as ci


PACKET = "linear-a4-collision-bins-r1"
INTAKE = Path("quartics/quartic-318-326/proof/intake") / PACKET
PROGRESS = Path("quartics/quartic-318-326/proof/progress")
EXPECTED = {
    "LinearA4GaussianCounts318": {
        "Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic",
        "Mathlib.Tactic",
    },
    "LinearA4MixedNormCounts318": {"LinearA4GaussianCounts318"},
    "LinearA4CollisionBins318": {
        "LinearA4MixedNormCounts318",
        "Mathlib.Algebra.Field.ZMod",
    },
}
MATHLIB_PIN = "56a005855ea17e0b0958f73ec801ae140b0a1679"
LEAN_VERSION = (
    "Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit "
    "eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)"
)
ALLOWED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
STRICT_FLAG = "-DwarningAsError=true"
SECONDS_PER_FILE = 180


def source_path(module):
    return (INTAKE if module == "LinearA4CollisionBins318" else PROGRESS) / (module + ".lean")


def read_packet(root=ci.ROOT):
    """Read canonical sources once; no fallback to a local build or sibling."""
    manifest_bytes = (root / INTAKE / "intake.json").read_bytes()
    data = json.loads(manifest_bytes)
    if data["order"] != list(EXPECTED):
        raise ValueError("Unexpected affine module order or scope")
    files = data["files"]
    if set(files) != {m + ".lean" for m in EXPECTED}:
        raise ValueError("Unexpected affine source filenames")
    bodies = {}
    for module, imports in EXPECTED.items():
        filename = module + ".lean"
        row = files[filename]
        if len(row["imports"]) != len(imports) or set(row["imports"]) != imports:
            raise ValueError("Unexpected declared imports: " + module)
        raw = (root / source_path(module)).read_bytes()
        if sha256(raw).hexdigest() != row["sha256"]:
            raise ValueError("Affine source hash mismatch: " + module)
        bodies[filename] = raw
    return manifest_bytes, bodies


@contextmanager
def admitted_packet(root=ci.ROOT):
    manifest, bodies = read_packet(root)
    with tempfile.TemporaryDirectory(prefix="lean-affine-intake-") as tmp:
        stage = Path(tmp) / PACKET
        stage.mkdir()
        (stage / "intake.json").write_bytes(manifest)
        for name, raw in bodies.items():
            (stage / name).write_bytes(raw)
        # No accepted local module is a valid dependency of this packet.
        folder, data, direct, upstream = experiment.packet(
            PACKET, {"module_keys": {}}, root=stage.parent
        )
        expected_upstream = set().union(*EXPECTED.values()) - set(EXPECTED)
        if direct or upstream != expected_upstream:
            raise ValueError("Nonempty project dependency or changed upstream closure")
        yield folder, data, sorted(upstream)


def revision(*args):
    return subprocess.check_output(
        ["git", "rev-parse", *args], cwd=ci.ROOT, text=True
    ).strip()


def check(output):
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    logs, lib = output / "logs", output / "lib"
    lib.mkdir()
    result = {
        "status": "PENDING",
        "scope": "Three fresh affine collision modules; not accepted baseline or full theorem",
        "platform": "linux-x86_64",
        "commands": [],
        "project_artifacts_reused": 0,
        "new_source_acceptance": False,
        "full_arithmetic_theorem_proved": False,
    }
    try:
        commit = revision("HEAD")
        if os.environ.get("GITHUB_SHA") != commit:
            raise ValueError("Checkout is not the exact hosted event commit")
        result.update(commit=commit, tree=revision("HEAD^{tree}"))
        with admitted_packet() as (folder, data, upstream):
            result.update(
                intake_sha256=ci.sha(folder / "intake.json"),
                sources=data["files"],
                source_paths={m: source_path(m).as_posix() for m in data["order"]},
                upstream_roots=upstream,
                lake_manifest_sha256=ci.sha(ci.PROJECT / "lake-manifest.json"),
                lean_toolchain_sha256=ci.sha(ci.PROJECT / "lean-toolchain"),
            )
            packages = json.loads((ci.PROJECT / "lake-manifest.json").read_bytes())["packages"]
            result["dependency_revisions"] = {p["name"]: p["rev"] for p in packages}
            if result["dependency_revisions"].get("mathlib") != MATHLIB_PIN:
                raise ValueError("Unexpected Mathlib lock")
            # This verifier removes inherited LEAN_PATH and checks every locked Git HEAD.
            env, compiler = ci.environment(ci.PROJECT, lib)
            if compiler != LEAN_VERSION:
                raise ValueError("Unexpected hosted toolchain: " + compiler)
            result["toolchain"] = compiler
            for name in upstream:
                rel = name.replace(".", "/") + ".olean"
                if not any((Path(p) / rel).is_file() for p in env["LEAN_PATH"].split(os.pathsep)):
                    raise ValueError("Missing pinned upstream artifact: " + name)

            opts = [*ci.FLAGS, STRICT_FLAG]
            result["lean_flags"] = opts
            original_flags = ci.FLAGS
            ci.FLAGS = opts
            try:
                for module in data["order"]:
                    row = experiment.compile_bounded(
                        folder / (module + ".lean"), lib / (module + ".olean"),
                        folder, env, logs, SECONDS_PER_FILE
                    )
                    result["commands"].append(row)
                    if row["exit_code"]:
                        raise RuntimeError("Strict compile failed: " + module)
                audit = output / "ExperimentAudit.lean"
                audit.write_text(experiment.audit_text(data["order"]), encoding="utf-8")
                row = experiment.compile_bounded(audit, None, output, env, logs, SECONDS_PER_FILE)
                result["commands"].append(row)
                if row["exit_code"]:
                    raise RuntimeError("Private recursive audit failed")
            finally:
                ci.FLAGS = original_flags

            log = (logs / "ExperimentAudit.log").read_text(encoding="utf-8")
            counts = re.findall(r"EXPERIMENT_AUDIT_PASS declarations=(\d+) modules=(\d+)", log)
            if len(counts) != 1 or int(counts[0][1]) != len(data["order"]) or int(counts[0][0]) <= 0:
                raise ValueError("Incomplete private recursive audit")
            result.update(
                status="PASS",
                freshly_compiled_project_modules=len(data["order"]),
                audited_declarations=int(counts[0][0]),
                allowed_axioms=ALLOWED_AXIOMS,
            )
    except Exception as error:
        result.update(status="FAIL", error=str(error))
        raise
    finally:
        ci.write_json(output / "RESULT.json", result)
        print(json.dumps(result), flush=True)


def main():
    if not __debug__:
        raise RuntimeError("Run without Python -O")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["targets", "check"])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.command == "targets":
        if args.output is not None:
            parser.error("--output is only for check")
        with admitted_packet() as (_, _, upstream):
            print("\n".join(upstream))
    else:
        if args.output is None:
            parser.error("check requires --output")
        check(args.output)


if __name__ == "__main__":
    main()
