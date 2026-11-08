#!/usr/bin/env python3
"""Dependency-closed CI cohorts with verified incremental Lean artifacts.

Cache artifacts are trusted outputs of this repository's CI, not independent
proof certificates. Every reuse is bound to the source, transitive dependencies,
toolchain, compiler flags, checker, and artifact bytes. A clean run bypasses reuse.
The final audit always imports the complete snapshot, including private declarations.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

from check_lean import code_only

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "quartics/quartic-318-326/proof/progress"
SCHEMA = 2
FLAGS = ["-j1", "-M", "6144", "-Ddebug.skipKernelTC=false"]
SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir")
OFFICIAL = [
    "Mathlib/RingTheory/Smooth/IntegralClosure",
    "Mathlib/CategoryTheory/Limits/Final/Type",
    "Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree",
    "Mathlib/Algebra/Category/ModuleCat/Differentials/Basic",
    "Mathlib/Algebra/Category/ModuleCat/Presheaf/OfCommRing",
    "Mathlib/Algebra/Category/ModuleCat/Differentials/Presheaf",
]


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def import_names(text):
    return {name for line in re.findall(
        r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([^\n]+)",
        code_only(text), re.M) for name in line.split()}


def partition_stage(order, dependencies, count):
    local = set(order)
    closure = {}
    for name in order:
        closure[name] = {name}.union(*(closure[d] for d in dependencies[name] if d in local))
    used = {d for n in order for d in dependencies[n] if d in local}
    sinks = sorted(local - used, key=lambda n: (-len(closure[n]), n))
    groups, roots = [set() for _ in range(count)], [[] for _ in range(count)]
    for name in sinks:
        i = min(range(count), key=lambda i: (
            4 * len(closure[name] - groups[i]) + len(groups[i]), len(groups[i]), i))
        groups[i].update(closure[name]); roots[i].append(name)
    return [(group, root) for group, root in zip(groups, roots) if group]


def derive_plan(project=PROJECT, count=16, split_depth=21):
    manifest = json.loads((project / "checkpoint-manifest.json").read_text())
    order = manifest["module_order"]
    if len(set(order)) != len(order) or set(order) != set(manifest["modules"]):
        raise ValueError("Module manifest/order mismatch")
    if json.loads((project / "module-order.json").read_text()) != order:
        raise ValueError("Replay module-order.json differs from the authoritative manifest")
    base = digest({"schema": SCHEMA, "platform": "linux-x86_64",
                   "toolchain": sha(project / "lean-toolchain"),
                   "dependencies": sha(project / "lake-manifest.json"),
                   "checker": sha(Path(__file__)), "parser": sha(ROOT / "scripts/check_lean.py"),
                   "flags": FLAGS})
    dependencies, closure, keys, upstream = {}, {}, {}, set()
    for name in order:
        if not re.fullmatch(r"[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*", name):
            raise ValueError(f"Invalid module name {name!r}")
        source = project / (name.replace(".", "/") + ".lean")
        source_hash = sha(source)
        if source_hash != manifest["modules"][name]["sha256"]:
            raise ValueError(f"Source hash mismatch: {name}")
        imports = import_names(source.read_text())
        dependencies[name] = sorted(imports.intersection(order))
        if any(dep not in keys for dep in dependencies[name]):
            raise ValueError(f"Non-topological import: {name}")
        upstream.update(x for x in imports if x not in manifest["modules"])
        closure[name] = {name}.union(*(closure[d] for d in dependencies[name]))
        keys[name] = digest({"base": base, "module": name, "source": source_hash,
                             "dependencies": {d: keys[d] for d in dependencies[name]}})
    audit_imports = import_names((project / "CheckpointAudit.lean").read_text())
    if audit_imports.intersection(order) != set(order):
        raise ValueError("Combined audit must import every snapshot module")
    depth = {}
    for name in order:
        depth[name] = max((depth[d] + 1 for d in dependencies[name]), default=0)
    cohorts = []
    for stage in range(2):
        members = [n for n in order if int(depth[n] >= split_depth) == stage]
        for slot, (group, roots) in enumerate(partition_stage(members, dependencies, count)):
            modules = [name for name in order if name in group]
            imports = set().union(*(closure[n] for n in modules)) - group
            cohorts.append({"id": len(cohorts), "stage": stage, "slot": slot,
                            "modules": modules, "imports": [n for n in order if n in imports], "roots": roots,
                            "key": digest([keys[n] for n in modules])})
    snapshot = digest({"base": base, "modules": keys, "audit": sha(project / "CheckpointAudit.lean")})
    return {"schema": SCHEMA, "base": base, "snapshot": snapshot, "module_order": order,
            "dependencies": dependencies, "module_keys": keys, "cohorts": cohorts,
            "upstream": sorted(upstream), "depth": depth, "cohort_count": count,
            "split_depth": split_depth, "audit_sha256": sha(project / "CheckpointAudit.lean")}


def check_sources(project):
    subprocess.run([sys.executable, "-B", str(project / "verify_manifest.py")], check=True)


def environment(project, lib):
    packages = json.loads((project / "lake-manifest.json").read_text())["packages"]
    libraries = []
    for package in packages:
        folder = project / ".lake/packages" / package["name"]
        actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=folder, text=True).strip()
        if actual != package["rev"]:
            raise ValueError(f"Dependency pin mismatch: {package['name']}")
        subprocess.run(["git", "diff", "--quiet", "HEAD", "--"], cwd=folder, check=True)
        library = folder / ".lake/build/lib/lean"
        if library.is_dir(): libraries.append(library)
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    if "version 4.35.0," not in version or "eb6cafb" not in version:
        raise ValueError(f"Unexpected compiler: {version}")
    env = os.environ.copy()
    env.pop("LEAN_SRC_PATH", None)
    # No inherited project library may supply an unchecked import.
    env["LEAN_PATH"] = os.pathsep.join(str(x) for x in [lib, *libraries])
    return env, version


def compile_one(project, env, label, source, target, logs, root=None):
    logs.mkdir(parents=True, exist_ok=True)
    args = ["lean", *FLAGS, "-R", str(root or project)]
    if target is not None:
        target.parent.mkdir(parents=True, exist_ok=True)
        args += ["-o", str(target)]
    args.append(str(source))
    start = time.monotonic()
    with (logs / (label.replace("/", "_") + ".log")).open("w") as log:
        result = subprocess.run(args, cwd=project, env=env, stdout=log,
                                stderr=subprocess.STDOUT, timeout=3600)
    row = {"module": label, "seconds": round(time.monotonic() - start, 3),
           "exit_code": result.returncode}
    print(json.dumps(row), flush=True)
    if result.returncode:
        raise RuntimeError(f"Kernel check failed: {label}; see uploaded log")
    return row


def ensure_official(project, env, logs):
    packages = [project / ".lake/packages" / p["name"] for p in
                json.loads((project / "lake-manifest.json").read_text())["packages"]]
    libraries = [p / ".lake/build/lib/lean" for p in packages]
    local_names = set(json.loads((project / "checkpoint-manifest.json").read_text())["module_order"])
    roots = {name.replace("/", ".") for name in OFFICIAL}
    for name in local_names:
        roots.update(import_names((project / (name.replace(".", "/") + ".lean")).read_text()) - local_names)
    visiting = set()
    def ensure(name):
        if name.split(".")[0] in {"Lean", "Init", "Std"}: return
        relative = name.replace(".", "/")
        if any((lib / (relative + ".olean")).is_file() for lib in libraries): return
        if name in visiting: raise ValueError(f"Upstream import cycle: {name}")
        package = next((p for p in packages if (p / (relative + ".lean")).is_file()), None)
        if package is None: raise ValueError(f"Missing pinned upstream source: {name}")
        visiting.add(name)
        source = package / (relative + ".lean")
        for dependency in sorted(import_names(source.read_text())): ensure(dependency)
        target = package / ".lake/build/lib/lean" / (relative + ".olean")
        lib = str(package / ".lake/build/lib/lean")
        if lib not in env["LEAN_PATH"].split(os.pathsep): env["LEAN_PATH"] += os.pathsep + lib
        compile_one(project, env, name, source, target, logs, package)
        visiting.remove(name)
    for name in sorted(roots): ensure(name)


def artifact_paths(lib, name):
    stem = lib / name.replace(".", "/")
    return {suffix: Path(str(stem) + suffix) for suffix in SUFFIXES}


def artifact_hashes(lib, name):
    paths = artifact_paths(lib, name)
    if not paths[".olean"].is_file(): raise ValueError(f"Missing olean: {name}")
    return {suffix: sha(path) for suffix, path in paths.items() if path.is_file()}


def reusable(entry, name, plan, cached_lib, built):
    if not isinstance(entry, dict) or entry.get("key") != plan["module_keys"][name]: return False
    expected_deps = {d: built[d]["files"] for d in plan["dependencies"][name]}
    if entry.get("dependency_artifacts") != expected_deps: return False
    try:
        return entry.get("files") == artifact_hashes(cached_lib, name)
    except (ValueError, OSError):
        return False


def copy_artifacts(source, target, name, expected):
    if ".olean" not in expected or not set(expected).issubset(SUFFIXES):
        raise ValueError(f"Invalid artifact list: {name}")
    src, dst = artifact_paths(source, name), artifact_paths(target, name)
    for suffix, digest_value in expected.items():
        if sha(src[suffix]) != digest_value: raise ValueError(f"Artifact hash mismatch: {name}{suffix}")
        dst[suffix].parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src[suffix], dst[suffix])


def save_cache(cache, lib, receipt):
    cache = cache.resolve()
    cache.mkdir(parents=True, exist_ok=True)
    cached_lib = cache / "lib"
    if cached_lib.exists(): shutil.rmtree(cached_lib)
    shutil.copytree(lib, cached_lib)
    write_json(cache / "receipt.json", receipt)


def build_cohort(args, plan):
    cohort = next(c for c in plan["cohorts"] if c["id"] == args.cohort)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    lib, logs = output / "lib", output / "logs"
    lib.mkdir()
    env, version = environment(PROJECT, lib)
    ensure_official(PROJECT, env, logs)
    cache = args.cache.resolve()
    candidates = []
    if not args.clean:
        for folder in [cache, getattr(args, "fallback_cache", None)]:
            if folder is None or not (folder / "receipt.json").is_file(): continue
            try:
                old = json.loads((folder / "receipt.json").read_text())
                if old.get("status") == "PASS" and old.get("base") == plan["base"]:
                    candidates.append((folder / "lib", old.get("modules", {})))
            except (ValueError, OSError):
                pass
    built, commands, hits = {}, [], []
    if cohort["imports"]:
        if args.bundles is None: raise ValueError("Dependent cohort requires earlier-stage bundles")
        prerequisites = [c for c in plan["cohorts"] if c["stage"] < cohort["stage"]]
        prior_entries, _, _, versions, origins = collect_bundles(
            args.bundles, plan, prerequisites, args.clean)
        if versions != {version}: raise ValueError("Earlier stage used a different compiler")
        for name in cohort["imports"]:
            built[name] = prior_entries[name]
            copy_artifacts(origins[name], lib, name, built[name]["files"])
    for name in cohort["modules"]:
        hit = next(((folder, prior[name]) for folder, prior in candidates
                    if reusable(prior.get(name), name, plan, folder, built)), None)
        if hit is not None:
            folder, entry = hit
            copy_artifacts(folder, lib, name, entry["files"])
            hits.append(name)
            print(json.dumps({"module": name, "cache": "verified-reuse"}), flush=True)
        else:
            commands.append(compile_one(PROJECT, env, name,
                PROJECT / (name.replace(".", "/") + ".lean"),
                artifact_paths(lib, name)[".olean"], logs))
        built[name] = {"key": plan["module_keys"][name], "files": artifact_hashes(lib, name),
                       "dependency_artifacts": {d: built[d]["files"] for d in plan["dependencies"][name]}}
        write_json(output / "commands.json", commands)
    receipt = {"schema": SCHEMA, "status": "PASS", "base": plan["base"],
               "snapshot": plan["snapshot"], "cohort": args.cohort, "cohort_key": cohort["key"],
               "stage": cohort["stage"],
               "mode": "clean" if args.clean else "incremental", "toolchain": version,
               "modules": {n: built[n] for n in cohort["modules"]}, "reused": hits, "compiled": [c["module"] for c in commands]}
    write_json(output / "receipt.json", receipt)
    # Earlier-stage imports are verified inputs, not this cohort's output/cache.
    for name in cohort["imports"]:
        for path in artifact_paths(lib, name).values():
            if path.exists(): path.unlink()
    # Only successfully validated/compiled files enter the next cache generation.
    save_cache(cache, lib, receipt)
    print(json.dumps({"cohort": args.cohort, "compiled": len(commands), "reused": len(hits)}), flush=True)


def collect_bundles(bundles, plan, cohorts, clean=False, lib=None):
    entries, reports, freshly_compiled, versions = {}, [], set(), set()
    origins = {}
    for cohort in cohorts:
        bundle = bundles / f"progress-cohort-{cohort['id']}"
        receipt = json.loads((bundle / "receipt.json").read_text())
        if any(receipt.get(k) != v for k, v in {"status": "PASS", "base": plan["base"],
               "snapshot": plan["snapshot"], "cohort_key": cohort["key"], "cohort": cohort["id"], "stage": cohort["stage"]}.items()):
            raise ValueError(f"Wrong cohort receipt: {cohort['id']}")
        if set(receipt["modules"]) != set(cohort["modules"]): raise ValueError("Cohort coverage mismatch")
        compiled, reused = set(receipt["compiled"]), set(receipt["reused"])
        if compiled.intersection(reused) or compiled.union(reused) != set(cohort["modules"]):
            raise ValueError("Incorrect compiled/reused partition")
        freshly_compiled.update(compiled)
        versions.add(receipt["toolchain"])
        if clean and (receipt["mode"] != "clean" or receipt["reused"]):
            raise ValueError("Clean audit cannot consume incremental cache reuse")
        for name in cohort["modules"]:
            item = receipt["modules"][name]
            if item["key"] != plan["module_keys"][name]: raise ValueError(f"Wrong source key: {name}")
            dep_artifacts = {d: (receipt["modules"].get(d) or entries[d])["files"]
                             for d in plan["dependencies"][name]}
            if item["dependency_artifacts"] != dep_artifacts: raise ValueError(f"Wrong dependency artifacts: {name}")
            if name in entries and entries[name] != item:
                raise ValueError(f"Cohorts produced different bytes for {name}; refusing mixed artifacts")
            if artifact_hashes(bundle / "lib", name) != item["files"]:
                raise ValueError(f"Corrupt cohort artifacts: {name}")
            if lib is not None: copy_artifacts(bundle / "lib", lib, name, item["files"])
            origins[name] = bundle / "lib"
            entries[name] = item
        reports.append({"id": cohort["id"], "compiled": len(receipt["compiled"]),
                        "reused": len(receipt["reused"])})
    return entries, reports, freshly_compiled, versions, origins


def merge_and_audit(args, plan):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    lib, logs = output / "lib", output / "logs"
    lib.mkdir()
    entries, reports, freshly_compiled, versions, _ = collect_bundles(
        args.bundles, plan, plan["cohorts"], args.clean, lib)
    if set(entries) != set(plan["module_order"]): raise ValueError("Incomplete combined source coverage")
    env, version = environment(PROJECT, lib)
    if versions != {version}: raise ValueError("Cohorts used a different compiler")
    ensure_official(PROJECT, env, logs)
    compile_one(PROJECT, env, "CheckpointAudit", PROJECT / "CheckpointAudit.lean", None, logs)
    text = (logs / "CheckpointAudit.log").read_text()
    match = re.search(r"CHECKPOINT_AUDIT_PASS declarations=(\d+) modules=(\d+)", text)
    if not match or int(match[2]) != len(plan["module_order"]): raise ValueError("Incomplete axiom audit")
    result = {"status": "PASS", "mode": "clean" if args.clean else "incremental",
              "snapshot": plan["snapshot"], "toolchain": version, "source_modules": len(entries),
              "audited_declarations": int(match[1]), "cohorts": reports,
              "unique_modules_freshly_compiled": len(freshly_compiled),
              "unique_modules_only_reused": len(entries) - len(freshly_compiled),
              "all_sources_freshly_rebuilt": len(freshly_compiled) == len(entries),
              "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
              "full_arithmetic_theorem_proved": False,
              "cache_trust": "Verified artifacts from repository CI; not independent proof certificates"}
    write_json(output / "RESULT.json", result)
    if getattr(args, "cache", None) is not None:
        save_cache(args.cache, lib, {"schema": SCHEMA, "status": "PASS",
            "base": plan["base"], "snapshot": plan["snapshot"], "modules": entries,
            "scope": "Complete source coverage and recursive axiom audit",
            "audit_result_sha256": sha(output / "RESULT.json")})
    print(json.dumps(result), flush=True)


def main():
    if not __debug__: raise RuntimeError("Run without Python -O")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["plan", "build", "audit", "cache-targets"])
    parser.add_argument("--cohorts", type=int, default=16, choices=range(1, 33))
    parser.add_argument("--max-parallel", type=int, default=16, choices=range(1, 33))
    parser.add_argument("--split-depth", type=int, default=21, choices=range(1, 1001))
    parser.add_argument("--cohort", type=int)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--cache", type=Path)
    parser.add_argument("--fallback-cache", type=Path)
    parser.add_argument("--bundles", type=Path)
    parser.add_argument("--clean", action="store_true")
    parser.add_argument("--github-output", type=Path)
    args = parser.parse_args()
    if args.command != "cache-targets": check_sources(PROJECT)
    plan = derive_plan(count=args.cohorts, split_depth=args.split_depth)
    if args.command == "plan":
        if args.output: write_json(args.output, plan)
        matrices = [{"include": [{"id": c["id"], "key": c["key"], "modules": len(c["modules"]),
                                    "stage": c["stage"], "slot": c["slot"]}
                                   for c in plan["cohorts"] if c["stage"] == stage]}
                    for stage in range(2)]
        print(json.dumps({"modules": len(plan["module_order"]), "matrices": matrices, "base": plan["base"]}))
        if args.github_output:
            with args.github_output.open("a") as out:
                for stage, matrix in enumerate(matrices):
                    out.write(f"matrix{stage}=" + json.dumps(matrix, separators=(",", ":")) + "\n")
                out.write("base=" + plan["base"] + "\nhas_stage1=" +
                          str(bool(matrices[1]["include"])).lower() + "\n")
                out.write(f"parallel={args.max_parallel}\n")
                out.write("snapshot=" + plan["snapshot"] + "\n")
    elif args.command == "cache-targets":
        print("\n".join(x for x in plan["upstream"] if x.split(".")[0] not in {"Lean", "Std", "Init"}))
    elif args.command == "build":
        if args.cohort is None or args.output is None or args.cache is None: parser.error("build requires --cohort, --output, --cache")
        build_cohort(args, plan)
    else:
        if args.output is None or args.bundles is None: parser.error("audit requires --output and --bundles")
        merge_and_audit(args, plan)


if __name__ == "__main__": main()
