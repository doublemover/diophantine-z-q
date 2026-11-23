#!/usr/bin/env python3
"""Shadow only: plan standalone packet impact, or replay source admissions together.

No native work is dispatched, replaced or certified. The released workflows and
their required checks are unchanged. A proposed source-only row is not a PASS.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

import check_standalone_intake as stock

SHA = re.compile(r"[0-9a-f]{40}")
INERT = frozenset({"README.md", "README-BACKUP.txt"})
WORKFLOW = ".github/workflows/progress-standalone-intake.yml"
RUNNER = "scripts/check_standalone_intake.py"
PROFILES = {
    "lean-core": "scripts/test_standalone_intake.py",
    "pinned-mathlib": "scripts/test_standalone_mathlib_intake.py",
}


def git(root, *args):
    return stock.git_at(root, *args)


def commit(root, value):
    if not isinstance(value, str) or not SHA.fullmatch(value) or value == "0" * 40:
        raise ValueError("not a complete nonzero commit SHA")
    if git(root, "cat-file", "-t", value).strip() != b"commit":
        raise ValueError("object is not a commit")


def tip(root, head):
    commit(root, head)
    if git(root, "rev-parse", "HEAD").decode().strip() != head:
        raise ValueError("head does not match local checkout")


def owners(registry):
    """Every registered source (including external donor paths) and manifest."""
    result = {}
    for packet, config in registry.items():
        for path in stock.source_paths(packet, config).values():
            result.setdefault(path, set()).add(packet)
    return result


def matrix_shape(workflow, registry):
    """Check duplicated matrix contracts; reject YAML shapes this prototype cannot read."""
    pattern = (r"^          - packet: ([a-z][a-z0-9-]*)\n"
               r"            profile: (lean-core|pinned-mathlib)\n"
               r"            root_count: ([0-9]+)$")
    rows = [(p, k, int(n)) for p, k, n in re.findall(pattern, workflow, re.M)]
    packet_keys = re.findall(r"^\s*- packet: (\S+)\s*$", workflow, re.M)
    expected = [(p, c["profile"], len(c["artifact_roots"])) for p, c in registry.items()]
    if rows != expected or packet_keys != list(registry):
        raise ValueError("workflow matrix differs from ordered registry/profile/root count")
    return rows


def diff_entries(raw):
    """Consume every NUL-delimited name/status pair. Unknowns fail closed."""
    if raw == b"":
        return []
    tokens = raw.split(b"\0")
    if tokens.pop() or len(tokens) % 2:
        raise ValueError("incomplete Git change list")
    return [(s.decode("ascii"), p.decode("utf-8")) for s, p in zip(tokens[::2], tokens[1::2])]


def classify(order, ownership, changes):
    reasons = {p: [] for p in order}
    full = []
    for status, path in changes:
        if status != "M":
            full.append(f"{status} {path}: tree/graph shape changed")
        elif path in ownership:
            for p in ownership[path]:
                reasons[p].append(path)
        elif path not in INERT:
            full.append(f"{path}: shared control or unreviewed path")
    return reasons, full


def verify_push(event, before, head):
    if not isinstance(event, dict) or not isinstance(event.get("repository"), dict):
        raise ValueError("missing push identity")
    if (event.get("before") != before or event.get("after") != head or
        event.get("ref") != stock.BRANCH or event["repository"].get("full_name") !=
        "doublemover/diophantine-z-q" or any(event.get(k) is not False for k in
                                           ("created", "deleted", "forced"))):
        raise ValueError("unexpected branch, repository, base/head or push kind")


def shadow(root, before, head, event=None):
    order = tuple(stock.ALLOWLIST)
    reasons = {p: [] for p in order}
    full = []
    count = None
    try:
        tip(root, head)
        commit(root, before)
        if event is not None:
            verify_push(event, before, head)
        if git(root, "merge-base", before, head).decode().strip() != before:
            raise ValueError("base not proved ancestor")
        if (Path(stock.__file__).read_bytes() != git(root, "show", head + ":" + RUNNER) or
            (root / RUNNER).read_bytes() != Path(stock.__file__).read_bytes()):
            raise ValueError("working packet registry does not match head")
        workflow = git(root, "show", head + ":" + WORKFLOW).decode()
        matrix_shape(workflow, stock.ALLOWLIST)
        # A frozen admission registry names the complete flat source closure of
        # each standalone packet; a changed registry/unknown source cannot trim.
        raw = git(root, "diff", "--no-ext-diff", "--no-textconv", "--no-renames",
                  "--name-status", "-z", before, head, "--")
        changes = diff_entries(raw)
        count = len(changes)
        reasons, full = classify(order, owners(stock.ALLOWLIST), changes)
    except (ValueError, OSError, subprocess.SubprocessError) as exc:
        full = ["cannot establish complete stable scope: " + str(exc)]
    return {
        "schema": 1, "scope": "standalone-shadow-plan-only", "before": before,
        "head": head, "input": "push-event" if event is not None else "local-git-pair",
        "change_count": count, "fallback_all": bool(full), "fallback_reasons": full,
        "enforcement": "none; existing workflow remains authoritative",
        "rows": [{"packet": p, "recommended": "native" if full or reasons[p] else "source-admission",
                  "touched_inputs": reasons[p], "verified": False} for p in order],
    }


def aggregate(root, head, hosted=False):
    """Exactly the stock source admission per packet; fixture battery once/profile.

    No runtime install, .olean restore, kernel subprocess or status mutation.
    Offline execution is never labeled a hosted receipt.
    """
    tip(root, head)
    if root.resolve() != stock.ROOT.resolve():
        raise ValueError("runner and checkout differ")
    if hosted:
        stock.hosted_identity(root, os.environ)
    matrix_shape(git(root, "show", head + ":" + WORKFLOW).decode(), stock.ALLOWLIST)
    paths = [RUNNER, *stock.HELPERS, *PROFILES.values()]
    for path in paths:
        if (root / path).read_bytes() != git(root, "show", head + ":" + path):
            raise ValueError("working source differs: " + path)
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    env.pop("PACKET", None)  # Aggregate fixtures must cover the whole selected profile.
    results, suites = [], {}
    for packet, config in stock.ALLOWLIST.items():
        profile = config["profile"]
        if profile not in suites:
            start = time.monotonic()
            p = subprocess.run([sys.executable, "-E", "-s", "-B", PROFILES[profile]], cwd=root,
                               env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               timeout=120)
            suites[profile] = {"ok": p.returncode == 0, "exit": p.returncode,
                               "seconds": round(time.monotonic() - start, 3),
                               "log_sha256": hashlib.sha256(p.stdout).hexdigest()}
            if p.returncode:
                print(p.stdout.decode(errors="replace")[-12288:], file=sys.stderr)
        row = {"packet": packet, "profile": profile, "scope": "source-admission-only",
               "native": False, "fixture_ok": suites[profile]["ok"], "ok": False}
        try:
            if not row["fixture_ok"]:
                raise ValueError("profile fixture failed")
            with stock.admitted(root, head, packet, config) as (_, data, audit):
                row.update(ok=True, module_order=data["order"],
                           validated_audit_source_sha256=hashlib.sha256(audit).hexdigest(),
                           upstream_targets=list(config["artifact_roots"]))
        except (ValueError, RuntimeError, OSError, subprocess.SubprocessError) as exc:
            row["error"] = str(exc)
        results.append(row)
    return {"schema": 1, "scope": "source-admission-only", "head": head,
            "origin": "hosted-push" if hosted else "offline-replay",
            "project_artifacts_reused": False, "native_checks": 0,
            "fixture_profiles": suites, "rows": results, "ok": all(r["ok"] for r in results)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subs = parser.add_subparsers(dest="command", required=True)
    plan = subs.add_parser("plan")
    plan.add_argument("--before", required=True)
    plan.add_argument("--head", required=True)
    plan.add_argument("--push-event", type=Path)
    replay = subs.add_parser("admit")
    replay.add_argument("--head", required=True)
    replay.add_argument("--hosted", action="store_true")
    args = parser.parse_args()
    if args.command == "plan":
        event = None
        if args.push_event is not None:
            try:
                event = json.loads(args.push_event.read_bytes())
                if not isinstance(event, dict):
                    event = {}
            except (OSError, ValueError):
                event = {}
        result = shadow(stock.ROOT, args.before, args.head, event)
    else:
        result = aggregate(stock.ROOT, args.head, args.hosted)
    print(json.dumps(result, indent=2))
    return int(result.get("ok") is False)


if __name__ == "__main__":
    sys.exit(main())
