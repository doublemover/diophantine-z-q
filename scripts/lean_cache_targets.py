#!/usr/bin/env python3
"""Print exact upstream cache roots for the pinned, freshly rebuilt Lean helpers.

This selects dependency artifacts only. It never caches or reuses project oleans.
Mathlib's cache command resolves the complete transitive import closure.
"""
from pathlib import Path
import hashlib
import json
import re

from check_lean import code_only

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "lean"


def imports(text):
    result = set()
    for line in re.findall(
        r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([^\n]+)",
        code_only(text), re.M,
    ):
        result.update(line.split())
    return result


def cache_targets(project=PROJECT):
    manifest = json.loads((project / "SOURCE_MANIFEST.json").read_text())
    files = []
    for row in manifest["files"]:
        path = project / row["path"]
        if hashlib.sha256(path.read_bytes()).hexdigest() != row["sha256"]:
            raise ValueError(f"Source manifest mismatch: {row['path']}")
        if "module" in row:
            files.append(path)
    files.extend([project / "ZInQ.lean", project / "Checks/Axioms.lean"])
    upstream = set().union(*(imports(path.read_text()) for path in files))
    upstream = {name for name in upstream
                if name.split(".")[0] not in {"ZInQ", "Lean", "Init", "Std"}}
    if not upstream:
        raise ValueError("No upstream dependency roots found")
    if any(not re.fullmatch(r"[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*", name)
           for name in upstream):
        raise ValueError("Unexpected upstream module syntax")
    return sorted(upstream)


if __name__ == "__main__":
    print("\n".join(cache_targets()))
