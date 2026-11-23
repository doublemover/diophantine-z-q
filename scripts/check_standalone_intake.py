#!/usr/bin/env python3
"""Exact, no-baseline hosted intake. Only the reviewed Lean-core row is enabled."""
import argparse
from contextlib import contextmanager
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]
INTAKES = "quartics/quartic-318-326/proof/intake"
OUTPUT = "build/progress-standalone-intake"
BRANCH = "refs/heads/add-quartic-318-326"
COMPILER_TEXT = (
    "Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit "
    "eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)"
)
TOOLCHAIN_DIR = "leanprover--lean4---v4.35.0"
FLAGS = ("-j1", "-M", "6144", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true")
TIMEOUT = 180
AXIOMS = ("propext", "Classical.choice", "Quot.sound")
HELPERS = {
    "scripts/check_lean.py": "2301207f5021b474faef1f4446db827f4bcc00f3ba2246916c7c0e53b5897e70",
    "scripts/check_progress_lean.py": "a569e3952820fe0736a39e24db289c57d9d7fe87b5be6a4f4561f2b1ba551b63",
    "scripts/check_progress_experiment.py": "4abfb411e506170329f1a8b7d982ff05278b90c9bc2980b0781c58be9e39c96f",
}
COMPILER_BLOBS = {
    ".github/actions/setup-pinned-lean/action.yml": "6d365c603a4d160665ec1626aa34e6f95fcfed41",
    "scripts/setup_pinned_lean.sh": "07e7ed817fc040c5507fd0f3b381702ccff59009",
    "lean/lean-toolchain": "a6aff065db2882c535684f8c5bcd4f16e9a23915",
    "quartics/quartic-318-326/proof/progress/lean-toolchain": "a6aff065db2882c535684f8c5bcd4f16e9a23915",
}
CORE_PACKET = "linear-a4-weighted-readback-core-r1"
CORE_MODULE = "LinearA4WeightedReadbackCoreSmoke318"
ALLOWLIST = {
    CORE_PACKET: {
        "profile": "lean-core",
        "source_base": "a32027a869fc1fc37004b4ad8482418b698b77be",
        "scope": "Standalone same-witness weighted-union combinatorics only",
        "manifest_sha256": "fc35cbfc056867715ece0db2a5a3d40d6a38eaaf1547e3bd1f9186fe8c9f67c5",
        "modules": (
            (CORE_MODULE, "557f908b4a9b184ea2e3dcdc8ec7bfd80daf09aef0e13565ece22465f2c3a396",
             ("Init.Data.List.Lemmas",)),
        ),
        "source_roots": ("Init.Data.List.Lemmas",),
        "artifact_roots": (),
        "audit_sha256": "0825e99f44816f0480ed2ff7d61ade073e86aebe76c512ab847ea06e53254c09",
    },
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return sha256(raw).hexdigest()


def git_at(root, *args):
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env.update(GIT_NO_REPLACE_OBJECTS="1", GIT_NO_LAZY_FETCH="1",
               GIT_TERMINAL_PROMPT="0")
    return subprocess.check_output(
        ["git", "--no-replace-objects", "-C", str(root), *args],
        env=env, timeout=30,
    )


def hosted_identity(root, env):
    required = {
        "GITHUB_ACTIONS": "true", "GITHUB_EVENT_NAME": "push", "GITHUB_REF": BRANCH,
        "RUNNER_OS": "Linux", "RUNNER_ARCH": "X64", "ImageOS": "ubuntu24",
    }
    require(all(env.get(k) == v for k, v in required.items()),
            "Expected the exact hosted feature-branch push on Ubuntu 24.04 x64")
    commit = env.get("GITHUB_SHA", "")
    require(re.fullmatch(r"[0-9a-f]{40}", commit) is not None, "Invalid hosted SHA")
    require(git_at(root, "rev-parse", "HEAD").decode().strip() == commit,
            "Hosted SHA does not match checkout")
    tree = git_at(root, "rev-parse", "HEAD^{tree}").decode().strip()
    return commit, tree


def tree_entries(root, commit, path):
    out = {}
    for raw in git_at(root, "ls-tree", "-r", "-z", commit, "--", path).split(b"\0"):
        if not raw:
            continue
        meta, name = raw.split(b"\t", 1)
        mode, kind, blob = meta.decode("ascii").split()
        out[name.decode("utf-8")] = (mode, kind, blob)
    return out


def checked_blob(root, commit, path, entry):
    mode, kind, blob = entry
    require(mode == "100644" and kind == "blob", "Not a regular source blob: " + path)
    require(re.fullmatch(r"[0-9a-f]{40}", blob) is not None, "Invalid blob ID")
    return git_at(root, "cat-file", "blob", blob)


def verify_helpers(root, commit):
    # Bind helpers before import; no byte from the working tree may override a pin.
    for path, expected in {**HELPERS, **COMPILER_BLOBS}.items():
        entry = tree_entries(root, commit, path).get(path)
        require(entry is not None, "Missing tracked helper: " + path)
        # setup_pinned_lean.sh may have standard executable Git mode.
        mode, kind, blob = entry
        require(kind == "blob" and mode in {"100644", "100755"},
                "Invalid helper mode: " + path)
        if path in COMPILER_BLOBS:
            require(blob == expected, "Changed compiler setup pin: " + path)
        target = root / path
        require(target.resolve() == target and target.is_file(), "Invalid helper path: " + path)
        raw = git_at(root, "cat-file", "blob", blob)
        require(target.read_bytes() == raw, "Working helper differs from tracked blob: " + path)
        if path in HELPERS:
            require(digest(raw) == expected, "Changed stock parser/checker: " + path)


def profile_contract(config):
    # A future reviewed pinned-mathlib profile belongs here and in
    # profile_environment, not in packet-controlled data or CLI overrides.
    require(config["profile"] == "lean-core", "Unimplemented runner profile")
    require(not config["artifact_roots"], "A Lean-core packet may not fetch artifacts")
    require(all(root.split(".")[0] in {"Init", "Lean", "Std"}
                for root in config["source_roots"]), "Non-core root in Lean-core profile")


def read_payload(root, commit, packet, config):
    folder = INTAKES + "/" + packet
    entries = tree_entries(root, commit, folder)
    names = ["intake.json", *(n + ".lean" for n, _, _ in config["modules"])]
    require(set(entries) == {folder + "/" + n for n in names},
            "Tracked intake filenames differ from exact scope")
    return {n: checked_blob(root, commit, folder + "/" + n, entries[folder + "/" + n])
            for n in names}


def validate_payload(config, payload):
    profile_contract(config)
    require(set(payload) == {"intake.json", *(n + ".lean" for n, _, _ in config["modules"])},
            "Payload names differ from allowlist")
    raw = payload["intake.json"]
    require(digest(raw) == config["manifest_sha256"], "Changed exact intake manifest")
    data = json.loads(raw)
    require(data["order"] == [n for n, _, _ in config["modules"]],
            "Module order differs from allowlist")
    expected = {}
    for n, expected_sha, imports in config["modules"]:
        filename = n + ".lean"
        require(digest(payload[filename]) == expected_sha, "Changed exact source: " + filename)
        expected[filename] = {"sha256": expected_sha, "imports": list(imports)}
    require(data["files"] == expected, "Manifest source metadata differs from allowlist")
    return data


@contextmanager
def admitted(root, commit, packet, config):
    profile_contract(config)
    verify_helpers(root, commit)
    # Keep these imports deferred until the tracked bytes have been checked.
    import check_progress_experiment as stock

    payload = read_payload(root, commit, packet, config)
    validate_payload(config, payload)
    with tempfile.TemporaryDirectory(prefix="quartic-standalone-intake-") as tmp:
        folder = Path(tmp) / packet
        folder.mkdir()
        for name, raw in payload.items():
            (folder / name).write_bytes(raw)
        _, data, direct, upstream = stock.packet(
            packet, {"module_keys": {}}, root=folder.parent
        )
        require(not direct and sorted(upstream) == list(config["source_roots"]),
                "Stock import closure differs from reviewed roots")
        audit = stock.audit_text(data["order"]).encode("utf-8")
        require(digest(audit) == config["audit_sha256"], "Changed private recursive audit")
        yield folder, data, audit


def profile_environment(config, lib, env):
    profile_contract(config)
    sanitize = ("LEAN_", "LAKE_", "ELAN_", "LD_", "DYLD_")
    result = {k: v for k, v in env.items() if not k.startswith(sanitize)}
    result["LEAN_PATH"] = str(lib)
    return result


def invoke(command, folder, env, log, timeout):
    started = time.monotonic()
    with log.open("wb") as handle:
        try:
            code = subprocess.run(command, cwd=folder, env=env, stdout=handle,
                                  stderr=subprocess.STDOUT, timeout=timeout).returncode
        except subprocess.TimeoutExpired:
            handle.write(b"\nWALL_CLOCK_LIMIT_EXCEEDED\n")
            code = 124
    return {"module": log.stem, "exit_code": code,
            "seconds": round(time.monotonic() - started, 3)}


def audit_count(log, expected_modules):
    markers = re.findall(r"EXPERIMENT_AUDIT_PASS declarations=(\d+) modules=(\d+)", log)
    require(len(markers) == 1 and int(markers[0][0]) > 0
            and int(markers[0][1]) == expected_modules,
            "Incomplete or duplicate private recursive audit marker")
    return int(markers[0][0])


def check(packet, config):
    out = ROOT / OUTPUT / packet
    require(out.resolve() == out, "Receipt output path must not contain symlinks")
    out.mkdir(parents=True, exist_ok=False)
    logs = out / "logs"
    logs.mkdir()
    result = {
        "status": "FAIL", "phase": "hosted-identity", "packet": packet,
        "profile": config["profile"], "scope": config["scope"],
        "allowlist_sha256": digest(json.dumps(ALLOWLIST, sort_keys=True).encode()),
        "source_base": config["source_base"], "lean_flags": list(FLAGS),
        "seconds_per_file": TIMEOUT, "seconds_for_audit": TIMEOUT,
        "project_artifacts_reused": 0, "commands": [],
        "new_source_acceptance": False, "full_arithmetic_theorem_proved": False,
    }
    try:
        commit, tree = hosted_identity(ROOT, os.environ)
        result.update(commit=commit, tree=tree, phase="source-admission")
        with admitted(ROOT, commit, packet, config) as (folder, data, audit):
            result.update(
                sources=data["files"], order=data["order"],
                intake_path=INTAKES + "/" + packet,
                intake_sha256=config["manifest_sha256"],
                roots=config["source_roots"], artifact_roots=config["artifact_roots"],
                audit_sha256=config["audit_sha256"], phase="compiler-identity",
            )
            lib = folder.parent / "lib"
            lib.mkdir()
            env = profile_environment(config, lib, os.environ)
            compiler = Path.home() / ".elan/toolchains" / TOOLCHAIN_DIR / "bin/lean"
            version = subprocess.check_output(
                [str(compiler), "--version"], cwd=folder, env=env, text=True, timeout=30
            ).strip()
            require(version == COMPILER_TEXT, "Unexpected native Lean executable")
            result.update(toolchain=version, phase="module-compile")
            args = [str(compiler), *FLAGS, "-R", str(folder)]
            for name in data["order"]:
                row = invoke([*args, "-o", str(lib / (name + ".olean")),
                              str(folder / (name + ".lean"))],
                             folder, env, logs / (name + ".log"), TIMEOUT)
                result["commands"].append(row)
                require(row["exit_code"] == 0, "Strict compile failed: " + name)
            result["phase"] = "private-recursive-audit"
            audit_path = folder / "ExperimentAudit.lean"
            audit_path.write_bytes(audit)
            (out / audit_path.name).write_bytes(audit)
            audit_log = logs / "ExperimentAudit.log"
            row = invoke([*args, str(audit_path)], folder, env, audit_log, TIMEOUT)
            result["commands"].append(row)
            require(row["exit_code"] == 0, "Private recursive audit failed")
            count = audit_count(audit_log.read_text(encoding="utf-8"), len(data["order"]))
            result.update(status="PASS", phase="complete", audited_declarations=count,
                          freshly_compiled_project_modules=len(data["order"]),
                          allowed_axioms=AXIOMS)
    except Exception as error:
        result["error"] = str(error)
        raise
    finally:
        (out / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("targets", "check"))
    parser.add_argument("--packet", required=True, choices=tuple(ALLOWLIST))
    args = parser.parse_args()
    config = ALLOWLIST[args.packet]
    if args.command == "check":
        check(args.packet, config)
    else:
        commit, _ = hosted_identity(ROOT, os.environ)
        with admitted(ROOT, commit, args.packet, config):
            for root in config["artifact_roots"]:
                print(root)


if __name__ == "__main__":
    main()
