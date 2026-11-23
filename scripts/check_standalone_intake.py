#!/usr/bin/env python3
"""Exact, no-baseline hosted intake for reviewed Lean-core and pinned-Mathlib leaves."""
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
PROGRESS = "quartics/quartic-318-326/proof/progress"
DEP_OUTPUT = "build/dependency-setup"
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
DEPENDENCY_BLOBS = {
    ".github/actions/setup-pinned-dependency-sources/action.yml": "8723e78867131af5a1f93a288ae97d8cefdf14a4",
}
DEPENDENCY_HELPER_SHA = "f927646b0f8f3a5ef1cd0575d9428677476af87a7ec9430ac9eec97199412695"
LAKE_LOCKS = {
    "lake-manifest.json": "a770787f33b5824f61a0731d59e67fca3f44a531b21d1fc1a804064c6fb54e58",
    "lakefile.toml": "908476df02b96238ec75ab9f7c953d7d5238b023b87e29a775709d4a62dc2d2a",
    "lean-toolchain": "ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c",
}
PACKAGE_REVISIONS = {
    "mathlib": "56a005855ea17e0b0958f73ec801ae140b0a1679",
    "plausible": "dfa4f38190d07c37e315953e08b90fe2d95b3c24",
    "LeanSearchClient": "d6b4c7be5be75ec4917c873ac50c756dc1436372",
    "importGraph": "a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93",
    "proofwidgets": "df72b022e558978a1c50264cfc4d7fec86fa8e04",
    "aesop": "4a174c490d8707121c4a9290800489f105d85e07",
    "Qq": "dce0ad79c486cb1fb504af04f953c3466b0c6db8",
    "batteries": "66e469188fe07963e5cf666c7d4433f45b8131c5",
    "Cli": "c24fe6078c630e89b489bffe59b3e20ac30d12c8",
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
        "audit_sha256": "f7c94ff210df496a78533346774d435bfe52b02765ba61947a3c8d0346977fce",
    },
    "pel-original-order-gram-r2": {
        "profile": "pinned-mathlib",
        "source_base": "a32027a869fc1fc37004b4ad8482418b698b77be",
        "scope": "Original fixed split order's signed integral Gram and covolume in the checked same-basis period convention; not marked analytification or full quartic",
        "manifest_sha256": "fb3329745b3bf4c57f3e004d903025c84a0677e4ffdfd1ac8a3ba9e49de55aad",
        "modules": (
            ("QuaternionicRealPeriod318",
             "996fc76819df4867affa9870c6bb24ce5303db9db4f0f6f164070ab922f8ddda",
             ("Mathlib.Analysis.Complex.Basic", "Mathlib.Data.Matrix.Basic", "Mathlib.LinearAlgebra.Matrix.ToLin", "Mathlib.Tactic")),
            ("SelectedActualPELPeriodColumns318",
             "b6d4ef954e793f054b547ff6ba9929fa7a56322ff8fd213df5fe287e215f73f8",
             ("Mathlib.LinearAlgebra.Basis.Defs", "Mathlib.LinearAlgebra.Matrix.Notation", "Mathlib.LinearAlgebra.Matrix.Trace", "Mathlib.Tactic", "QuaternionicRealPeriod318")),
            ("SelectedSameAOriginalOrderGram318",
             "681a346e26b368f23cf1cf75d03394f11e5ba1669757ac3aaecdf0b40740bd8f",
             ("Mathlib.Analysis.SpecialFunctions.Sqrt", "Mathlib.LinearAlgebra.Matrix.Determinant.Basic", "Mathlib.Tactic", "SelectedActualPELPeriodColumns318")),
        ),
        "source_roots": (
            "Mathlib.Analysis.Complex.Basic",
            "Mathlib.Analysis.SpecialFunctions.Sqrt",
            "Mathlib.Data.Matrix.Basic",
            "Mathlib.LinearAlgebra.Basis.Defs",
            "Mathlib.LinearAlgebra.Matrix.Determinant.Basic",
            "Mathlib.LinearAlgebra.Matrix.Notation",
            "Mathlib.LinearAlgebra.Matrix.ToLin",
            "Mathlib.LinearAlgebra.Matrix.Trace",
            "Mathlib.Tactic",
        ),
        "artifact_roots": (
            "Mathlib.Analysis.Complex.Basic",
            "Mathlib.Analysis.SpecialFunctions.Sqrt",
            "Mathlib.Data.Matrix.Basic",
            "Mathlib.LinearAlgebra.Basis.Defs",
            "Mathlib.LinearAlgebra.Matrix.Determinant.Basic",
            "Mathlib.LinearAlgebra.Matrix.Notation",
            "Mathlib.LinearAlgebra.Matrix.ToLin",
            "Mathlib.LinearAlgebra.Matrix.Trace",
            "Mathlib.Tactic",
        ),
        "audit_sha256": "55aff9c9cb217636677befc1370c55e1b73172ec5a3055991ffa9ddcf8f40dac",
        "predecessor_source_commit": "a872d819a4a555fde19debe8233443876602e430",
        "source_paths": {
            "QuaternionicRealPeriod318": "quartics/quartic-318-326/proof/intake/pel-period-columns-corrected-r2/QuaternionicRealPeriod318.lean",
            "SelectedActualPELPeriodColumns318": "quartics/quartic-318-326/proof/intake/pel-period-columns-corrected-r2/SelectedActualPELPeriodColumns318.lean",
        },
    },
    "finite-height-dlog-mapped-trait-r1": {
        "profile": "pinned-mathlib",
        "source_base": "5c4ff737b79b8b481eb8beaff84134a9fb2ed4b8",
        "scope": "Four-source finite coefficient attachment for a given regular chart map, dlog equations and integral multiplier; no original model, height or endpoint",
        "manifest_sha256": "ed60f42192ee4298100d55c5381eaa3ffb98f68860a9e3a8fc0bec506760cd68",
        "modules": (
            ("SquareReflection318", "eac90b36f3f364cb003142fe184eb9f4e55e809ec874f108eb120f9ff9efc41f",
             ("Mathlib.Algebra.QuadraticAlgebra.Basic", "Mathlib.RingTheory.IntegralClosure.IntegrallyClosed", "Mathlib.Tactic")),
            ("LinearContactSquareclass318", "741bef76f07ed956f8d8a36d0b1986e200369b47671c1e240f8847066dfb494e",
             ("Mathlib.Algebra.Polynomial.RingDivision", "Mathlib.Algebra.Squarefree.Basic", "Mathlib.FieldTheory.RatFunc.Basic", "SquareReflection318")),
            ("SelectedActualSameAFiniteDlogRows318", "15f2e7c3b8caf41f3410f37daf914d9471c7a39d17703faa9284c711a7dd0ae6",
             ("LinearContactSquareclass318", "Mathlib.Tactic")),
            ("SelectedActualSameAFiniteMappedDlogRows318", "ecc63d9aa47943ed1ab438de8652e389bacb281bfc6a774eab8e5b694e3c5585",
             ("Mathlib.NumberTheory.NumberField.Completion.FinitePlace", "SelectedActualSameAFiniteDlogRows318")),
        ),
        "source_roots": (
            "Mathlib.Algebra.Polynomial.RingDivision",
            "Mathlib.Algebra.QuadraticAlgebra.Basic",
            "Mathlib.Algebra.Squarefree.Basic",
            "Mathlib.FieldTheory.RatFunc.Basic",
            "Mathlib.NumberTheory.NumberField.Completion.FinitePlace",
            "Mathlib.RingTheory.IntegralClosure.IntegrallyClosed",
            "Mathlib.Tactic",
        ),
        "artifact_roots": (
            "Mathlib.Algebra.Polynomial.RingDivision",
            "Mathlib.Algebra.QuadraticAlgebra.Basic",
            "Mathlib.Algebra.Squarefree.Basic",
            "Mathlib.FieldTheory.RatFunc.Basic",
            "Mathlib.NumberTheory.NumberField.Completion.FinitePlace",
            "Mathlib.RingTheory.IntegralClosure.IntegrallyClosed",
            "Mathlib.Tactic",
        ),
        "audit_sha256": "830d60158d82e9b6255224a1040ade09ab4d6ce541a3d504280da05413b1b5c6",
        "predecessor_source_commit": "5c4ff737b79b8b481eb8beaff84134a9fb2ed4b8",
        "source_paths": {
            "SquareReflection318": "quartics/quartic-318-326/proof/intake/finite-height-dlog-rows-r4/SquareReflection318.lean",
            "LinearContactSquareclass318": "quartics/quartic-318-326/proof/intake/finite-height-dlog-rows-r4/LinearContactSquareclass318.lean",
            "SelectedActualSameAFiniteDlogRows318": "quartics/quartic-318-326/proof/intake/finite-height-dlog-rows-r4/SelectedActualSameAFiniteDlogRows318.lean",
        },
    },
    "same-j-direct-lenstra-clear-r2": {
        "profile": "pinned-mathlib",
        "source_base": "a32027a869fc1fc37004b4ad8482418b698b77be",
        "scope": "Exact signed-factor strict principal ideal containment and multiplier membership; no signed cover constructor or endpoint",
        "manifest_sha256": "7ae4f4e7933a323405c310a2225b943434f643ffd90d9638ec345ab91342dc36",
        "modules": (
            ("SelectedJOneDirectLenstraClear318", "ff2077f089a9ccb78ab0d9a5ac42f8268b32edb7c8b5321d0b0bf518237f1133",
             ("Mathlib.NumberTheory.Padics.PadicVal.Basic", "Mathlib.RingTheory.Coprime.Lemmas", "Mathlib.RingTheory.DedekindDomain.Different", "Mathlib.RingTheory.Valuation.ValuationRing", "Mathlib.Tactic")),
        ),
        "source_roots": (
            "Mathlib.NumberTheory.Padics.PadicVal.Basic",
            "Mathlib.RingTheory.Coprime.Lemmas",
            "Mathlib.RingTheory.DedekindDomain.Different",
            "Mathlib.RingTheory.Valuation.ValuationRing",
            "Mathlib.Tactic",
        ),
        "artifact_roots": (
            "Mathlib.NumberTheory.Padics.PadicVal.Basic",
            "Mathlib.RingTheory.Coprime.Lemmas",
            "Mathlib.RingTheory.DedekindDomain.Different",
            "Mathlib.RingTheory.Valuation.ValuationRing",
            "Mathlib.Tactic",
        ),
        "audit_sha256": "48dc0470e8e6728951a7cd8a5ec079d10bc981580252fd5f15bb670117b70185",
    },
    "pel-actual-marking-crt-r3": {
        "profile": "pinned-mathlib",
        "source_base": "a32027a869fc1fc37004b4ad8482418b698b77be",
        "scope": "Exact CRT merge and restriction of supplied torsion markings; no original moduli classifier, occurrence or endpoint",
        "manifest_sha256": "392348d6e395f6d24dc96588edf4be2ab47a153710f05266940d751c91ae0904",
        "modules": (
            ("SelectedPELMarkingCRT318", "b611a6f4bf21b79e3432dd43659d95fe9f4879a061b6082e7270c0dfed6089f9",
             ("Mathlib.Algebra.Group.Prod", "Mathlib.Algebra.Group.Subgroup.Basic", "Mathlib.Algebra.Module.NatInt", "Mathlib.Algebra.Ring.Equiv", "Mathlib.Algebra.Ring.Prod", "Mathlib.Data.ZMod.Basic")),
        ),
        "source_roots": (
            "Mathlib.Algebra.Group.Prod",
            "Mathlib.Algebra.Group.Subgroup.Basic",
            "Mathlib.Algebra.Module.NatInt",
            "Mathlib.Algebra.Ring.Equiv",
            "Mathlib.Algebra.Ring.Prod",
            "Mathlib.Data.ZMod.Basic",
        ),
        "artifact_roots": (
            "Mathlib.Algebra.Group.Prod",
            "Mathlib.Algebra.Group.Subgroup.Basic",
            "Mathlib.Algebra.Module.NatInt",
            "Mathlib.Algebra.Ring.Equiv",
            "Mathlib.Algebra.Ring.Prod",
            "Mathlib.Data.ZMod.Basic",
        ),
        "audit_sha256": "da826d79bec5f71318d2ca42dd29e5d77ab8b9e4851ee2f9c4f0dbdca38f00ec",
        "audit_public_meta": True,
    },
    "same-j-crt-trace-r2": {
        "profile": "pinned-mathlib",
        "source_base": "a32027a869fc1fc37004b4ad8482418b698b77be",
        "scope": "Arbitrary-ideal trace reduction and CRT trace detects the positive rank of the selected factor; stock algebra only",
        "manifest_sha256": "92bf47604b687d35e1a2281587ad2bfa9c963ad078c2de7bab9f56e5553b8c0a",
        "modules": (
            ("SelectedJOneCRTTrace318", "48c1f85b81c76098fe68b520bcbe59471c4302ad1c59319e41a46e72350c6036",
             ("Mathlib.LinearAlgebra.Dimension.Constructions", "Mathlib.RingTheory.LocalRing.Module", "Mathlib.RingTheory.TensorProduct.Finite", "Mathlib.RingTheory.TensorProduct.Quotient", "Mathlib.RingTheory.Trace.Basic")),
        ),
        "source_roots": (
            "Mathlib.LinearAlgebra.Dimension.Constructions",
            "Mathlib.RingTheory.LocalRing.Module",
            "Mathlib.RingTheory.TensorProduct.Finite",
            "Mathlib.RingTheory.TensorProduct.Quotient",
            "Mathlib.RingTheory.Trace.Basic",
        ),
        "artifact_roots": (
            "Mathlib.LinearAlgebra.Dimension.Constructions",
            "Mathlib.RingTheory.LocalRing.Module",
            "Mathlib.RingTheory.TensorProduct.Finite",
            "Mathlib.RingTheory.TensorProduct.Quotient",
            "Mathlib.RingTheory.Trace.Basic",
        ),
        "audit_sha256": "090cf72179e1524a42abf3c73879b4fa539b8923ae06ba93b07319a41755fcbe",
        "audit_public_meta": True,
    },
    "same-j-crt-different-r1": {
        "profile": "pinned-mathlib",
        "source_base": "a32027a869fc1fc37004b4ad8482418b698b77be",
        "scope": "Actual finite-free Dedekind branch CRT and exact multiplier membership in the uncompleted different; no geometric signed-cover construction",
        "manifest_sha256": "0e80b953c29756b77131cbe1192077abfb2490d0f469ff0b1bdd8f3f0f1136a6",
        "modules": (
            ("SelectedJOneDirectLenstraClear318", "ff2077f089a9ccb78ab0d9a5ac42f8268b32edb7c8b5321d0b0bf518237f1133",
             ("Mathlib.NumberTheory.Padics.PadicVal.Basic", "Mathlib.RingTheory.Coprime.Lemmas", "Mathlib.RingTheory.DedekindDomain.Different", "Mathlib.RingTheory.Valuation.ValuationRing", "Mathlib.Tactic")),
            ("SelectedJOneCRTTrace318", "48c1f85b81c76098fe68b520bcbe59471c4302ad1c59319e41a46e72350c6036",
             ("Mathlib.LinearAlgebra.Dimension.Constructions", "Mathlib.RingTheory.LocalRing.Module", "Mathlib.RingTheory.TensorProduct.Finite", "Mathlib.RingTheory.TensorProduct.Quotient", "Mathlib.RingTheory.Trace.Basic")),
            ("SelectedJOneCRTDifferent318", "86b72606e800c07b4cf60b3023a11378684b41b3bdf5b95b11b004ac9219f43b",
             ("SelectedJOneDirectLenstraClear318", "SelectedJOneCRTTrace318")),
        ),
        "source_roots": (
            "Mathlib.LinearAlgebra.Dimension.Constructions",
            "Mathlib.NumberTheory.Padics.PadicVal.Basic",
            "Mathlib.RingTheory.Coprime.Lemmas",
            "Mathlib.RingTheory.DedekindDomain.Different",
            "Mathlib.RingTheory.LocalRing.Module",
            "Mathlib.RingTheory.TensorProduct.Finite",
            "Mathlib.RingTheory.TensorProduct.Quotient",
            "Mathlib.RingTheory.Trace.Basic",
            "Mathlib.RingTheory.Valuation.ValuationRing",
            "Mathlib.Tactic",
        ),
        "artifact_roots": (
            "Mathlib.LinearAlgebra.Dimension.Constructions",
            "Mathlib.NumberTheory.Padics.PadicVal.Basic",
            "Mathlib.RingTheory.Coprime.Lemmas",
            "Mathlib.RingTheory.DedekindDomain.Different",
            "Mathlib.RingTheory.LocalRing.Module",
            "Mathlib.RingTheory.TensorProduct.Finite",
            "Mathlib.RingTheory.TensorProduct.Quotient",
            "Mathlib.RingTheory.Trace.Basic",
            "Mathlib.RingTheory.Valuation.ValuationRing",
            "Mathlib.Tactic",
        ),
        "audit_sha256": "99006f0a83118a074a47116db0ae3f6a5966b6951d8fbbc82dd85e617febba30",
        "predecessor_source_commit": "c9f78ff2f297348175935255b39decc08f119c86",
        "source_paths": {
            "SelectedJOneDirectLenstraClear318": "quartics/quartic-318-326/proof/intake/same-j-direct-lenstra-clear-r2/SelectedJOneDirectLenstraClear318.lean",
            "SelectedJOneCRTTrace318": "quartics/quartic-318-326/proof/intake/same-j-crt-trace-r2/SelectedJOneCRTTrace318.lean",
        },
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


def verify_helpers(root, commit, profile):
    # Bind helpers before import; no byte from the working tree may override a pin.
    sha_pins = dict(HELPERS)
    blob_pins = dict(COMPILER_BLOBS)
    if profile == "pinned-mathlib":
        sha_pins.update({PROGRESS + "/" + n: sha for n, sha in LAKE_LOCKS.items()})
        sha_pins["scripts/pinned_dependency_sources.py"] = DEPENDENCY_HELPER_SHA
        blob_pins.update(DEPENDENCY_BLOBS)
    for path in sorted(sha_pins.keys() | blob_pins.keys()):
        entry = tree_entries(root, commit, path).get(path)
        require(entry is not None, "Missing tracked helper: " + path)
        mode, kind, blob = entry
        require(kind == "blob" and mode in {"100644", "100755"},
                "Invalid helper mode: " + path)
        if path in blob_pins:
            require(blob == blob_pins[path], "Changed setup pin: " + path)
        target = root / path
        require(target.resolve() == target and target.is_file(), "Invalid helper path: " + path)
        raw = git_at(root, "cat-file", "blob", blob)
        require(target.read_bytes() == raw, "Working helper differs from tracked blob: " + path)
        if path in sha_pins:
            require(digest(raw) == sha_pins[path], "Changed locked helper/input: " + path)


def profile_contract(config):
    profile = config["profile"]
    roots = config["source_roots"]
    fetched = config["artifact_roots"]
    require(profile in {"lean-core", "pinned-mathlib"} and
            (profile != "pinned-mathlib" or bool(fetched)),
            "Unimplemented runner profile or missing pinned package roots")
    require(tuple(sorted(set(roots))) == roots, "Root list is not sorted unique")
    if profile == "lean-core":
        require(not fetched, "A Lean-core packet may not fetch artifacts")
        require(all(root.split(".")[0] in {"Init", "Lean", "Std"} for root in roots),
                "Non-core root in Lean-core profile")
    else:
        require(tuple(r for r in roots if not r.startswith(("Init.", "Lean.", "Std."))) == fetched
                and all(re.fullmatch(r"Mathlib(?:\.[A-Za-z0-9_]+)+", r) for r in fetched),
                "Pinned Mathlib roots differ from admitted non-core imports")


def source_paths(packet, config):
    require(re.fullmatch(r"[a-z][a-z0-9-]*", packet) is not None, "Invalid packet slug")
    folder = INTAKES + "/" + packet
    modules = [n for n, _, _ in config["modules"]]
    require(len(set(modules)) == len(modules) and
            all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", n) for n in modules),
            "Invalid reviewed module order")
    donors = config.get("source_paths", {})
    require(set(donors) <= set(modules), "External source assigned to an unlisted module")
    files = {"intake.json": folder + "/intake.json"}
    for n in modules:
        file = n + ".lean"
        local = folder + "/" + file
        path = donors.get(n, local)
        if n in donors:
            require(path != local and re.fullmatch(
                re.escape(INTAKES) + r"/[a-z][a-z0-9-]*/" + re.escape(file), path
            ) is not None, "Invalid static external donor path: " + n)
        files[file] = path
    return files


def read_payload(root, commit, packet, config):
    folder = INTAKES + "/" + packet
    files = source_paths(packet, config)
    entries = tree_entries(root, commit, folder)
    require(set(entries) == {p for p in files.values() if p.startswith(folder + "/")},
            "Tracked intake filenames differ from exact scope")
    payload = {}
    for name, path in files.items():
        entry = entries.get(path) if path.startswith(folder + "/") else tree_entries(
            root, commit, path
        ).get(path)
        require(entry is not None, "Missing exact tracked source: " + path)
        payload[name] = checked_blob(root, commit, path, entry)
    return payload


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
    verify_helpers(root, commit, config["profile"])
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
        audit_source = stock.audit_text(data["order"])
        if config["profile"] == "lean-core" or config.get("audit_public_meta") is True:
            # run_cmd elaborates a meta _eval. Without Mathlib.Tactic, both
            # the command instances and collector need public meta visibility.
            header = "import Lean.Util.CollectAxioms\n"
            require(audit_source.count(header) == 1, "Unexpected stock audit header")
            meta_header = ("public meta import Lean\n"
                           "public meta import Lean.Elab.Command\n"
                           "public meta import Lean.Util.CollectAxioms\n")
            audit_source = audit_source.replace(header, meta_header, 1)
        audit = audit_source.encode("utf-8")
        require(digest(audit) == config["audit_sha256"], "Changed private recursive audit")
        yield folder, data, audit


def profile_environment(config, lib, env, upstream=()):
    profile_contract(config)
    require((not upstream) == (config["profile"] == "lean-core"),
            "Profile and package library path disagree")
    sanitize = ("LEAN_", "LAKE_", "ELAN_", "LD_", "DYLD_")
    result = {k: v for k, v in env.items() if not k.startswith(sanitize)}
    result["LEAN_PATH"] = os.pathsep.join(str(path) for path in (lib, *upstream))
    return result


def regular_bytes(path):
    require(path.resolve() == path and path.is_file(), "Missing/redirected path: " + str(path))
    return path.read_bytes()


def validate_setup_receipts(config, targets, sources, artifacts):
    identity = LAKE_LOCKS | {"protocol": 1, "helper_sha256": DEPENDENCY_HELPER_SHA}
    require(targets == "".join(r + "\n" for r in config["artifact_roots"]).encode("ascii"),
            "Artifact target file differs from reviewed roots")
    for actual, mode in ((sources, "sources"), (artifacts, "artifacts")):
        require(actual.get("status") == "PASS" and actual.get("mode") == mode and
                actual.get("proof_check_run") is False and actual.get("identity") == identity,
                "Missing exact successful " + mode + " setup receipt")
    rows = sources.get("packages", [])
    require(len(rows) == len(PACKAGE_REVISIONS) and
            {p["name"]: p["rev"] for p in rows} == PACKAGE_REVISIONS,
            "Wrong package revisions in source setup receipt")
    attempts = artifacts.get("attempts", [])
    require(attempts and attempts[-1].get("label") == "upstream-artifacts" and
            attempts[-1].get("exit_code") == 0, "No successful pinned artifact acquisition")


def mathlib_setup(root, packet, config):
    project = root / PROGRESS
    lock = {}
    for name, pin in LAKE_LOCKS.items():
        raw = regular_bytes(project / name)
        require(digest(raw) == pin, "Changed runtime package lock: " + name)
        if name == "lake-manifest.json":
            lock = json.loads(raw)
    require(lock.get("packagesDir") == ".lake/packages" and lock.get("lakeDir") == ".lake",
            "Unexpected locked package layout")
    package_rows = lock["packages"]
    require(len(package_rows) == len(PACKAGE_REVISIONS) and
            {p["name"]: p["rev"] for p in package_rows} == PACKAGE_REVISIONS,
            "Unexpected package lock revisions")
    setup = root / DEP_OUTPUT
    targets = setup / (packet + ".targets.txt")
    sources = setup / "sources.json"
    artifacts = setup / (packet + ".artifacts.json")
    sources_raw, artifacts_raw, targets_raw = map(regular_bytes, (sources, artifacts, targets))
    validate_setup_receipts(config, targets_raw, json.loads(sources_raw), json.loads(artifacts_raw))
    packages = project / ".lake/packages"
    require(packages.resolve() == packages and packages.is_dir(), "Invalid verified package directory")
    upstream = []
    for p in package_rows:
        folder = packages / p["name"]
        require(folder.resolve() == folder and (folder / ".git").is_dir() and
                not (folder / ".git").is_symlink(), "Not a fresh real package checkout: " + p["name"])
        require(git_at(folder, "rev-parse", "HEAD").decode().strip() == p["rev"],
                "Wrong package HEAD: " + p["name"])
        require(git_at(folder, "remote", "get-url", "origin").decode().strip() == p["url"],
                "Wrong package remote: " + p["name"])
        git_at(folder, "diff", "--quiet", "HEAD", "--")
        lib = folder / ".lake/build/lib/lean"
        require(lib.resolve() == lib, "Redirected package Lean library: " + p["name"])
        if lib.is_dir():
            upstream.append(lib)
    mathlib = packages / "mathlib/.lake/build/lib/lean"
    require(mathlib in upstream, "Missing pinned Mathlib library")
    for name in config["artifact_roots"]:
        target = mathlib / (name.replace(".", "/") + ".olean")
        require(target.resolve() == target and target.is_file(),
                "Missing pinned upstream artifact: " + name)
    return tuple(upstream), {
        "upstream_policy": "Pinned package sources and upstream Mathlib cache; no project artifacts",
        "dependency_revisions": PACKAGE_REVISIONS,
        "dependency_receipts": {
            "sources_sha256": digest(sources_raw),
            "artifacts_sha256": digest(artifacts_raw),
            "targets_sha256": digest(targets_raw),
        },
    }


def print_failure_excerpt(log, max_lines=60, max_bytes=24 * 1024):
    """Show a bounded tail without treating compiler output as Actions commands."""
    with log.open("rb") as handle:
        length = handle.seek(0, os.SEEK_END)
        skipped = max(0, length - max_bytes)
        handle.seek(skipped)
        raw = handle.read(max_bytes)
    lines = raw.decode("utf-8", errors="replace").splitlines()
    if skipped and len(lines) > 1:
        # The first sampled line may start partway through an exact log line.
        lines = lines[1:]
    tail = lines[-max_lines:]
    print(f"Lean failure excerpt ({log.name}; last {len(tail)} lines; full log in artifact):")
    for line in tail:
        clean = re.sub(r"[\x00-\x08\x0b-\x1f\x7f]", "?", line)
        print("| " + clean)
    print("End Lean failure excerpt.", flush=True)


def invoke(command, folder, env, log, timeout):
    started = time.monotonic()
    with log.open("wb") as handle:
        try:
            code = subprocess.run(command, cwd=folder, env=env, stdout=handle,
                                  stderr=subprocess.STDOUT, timeout=timeout).returncode
        except subprocess.TimeoutExpired:
            handle.write(b"\nWALL_CLOCK_LIMIT_EXCEEDED\n")
            code = 124
    seconds = round(time.monotonic() - started, 3)
    if code:
        print_failure_excerpt(log)
    return {"module": log.stem, "exit_code": code, "seconds": seconds}


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
                source_paths=source_paths(packet, config),
                intake_path=INTAKES + "/" + packet,
                intake_sha256=config["manifest_sha256"],
                roots=config["source_roots"], artifact_roots=config["artifact_roots"],
                audit_sha256=config["audit_sha256"], phase="compiler-identity",
            )
            lib = folder.parent / "lib"
            lib.mkdir()
            upstream = ()
            if config["profile"] == "pinned-mathlib":
                result["phase"] = "pinned-upstream-setup"
                upstream, provenance = mathlib_setup(ROOT, packet, config)
                result.update(provenance)
                result["phase"] = "compiler-identity"
            if "predecessor_source_commit" in config:
                result["predecessor_source_commit"] = config["predecessor_source_commit"]
            env = profile_environment(config, lib, os.environ, upstream)
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
            try:
                count = audit_count(audit_log.read_text(encoding="utf-8"), len(data["order"]))
            except (ValueError, UnicodeError):
                print_failure_excerpt(audit_log)
                raise
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
