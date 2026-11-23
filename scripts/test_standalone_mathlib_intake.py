#!/usr/bin/env python3
"""Exact Mathlib admission and dependency-reader fixtures. No tools are installed."""
from copy import deepcopy
import json
import hashlib
import re
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check_standalone_intake as runner


GRAM = "pel-original-order-gram-r2"
DLOG = "finite-height-dlog-mapped-trait-r1"
LENSTRA = "same-j-direct-lenstra-clear-r2"
CRT = "pel-actual-marking-crt-r3"
TRACE = "same-j-crt-trace-r2"
DIFFERENT = "same-j-crt-different-r1"
TWIST = "forward-detached-twist-point-r3"
STRUCTURAL = "same-j-structural-normalization-r3"
DYADIC = "finite-plus11-dyadic-vertical-r2"
REFLECT = "raw318-input-reflection-r1"
OBSERVED = "linear-a4-signed-observed-r1"
EXPECTED = {GRAM: 9, DLOG: 7, LENSTRA: 5, CRT: 6, TRACE: 5, DIFFERENT: 10, TWIST: 4, STRUCTURAL: 3, DYADIC: 12, REFLECT: 4, OBSERVED: 3}
FRESH = {GRAM: 3, DLOG: 4, LENSTRA: 1, CRT: 1, TRACE: 1, DIFFERENT: 3, TWIST: 2, STRUCTURAL: 1, DYADIC: 5, REFLECT: 7, OBSERVED: 5}


def packets():
    requested = os.environ.get("PACKET")
    if requested is None:
        return tuple(EXPECTED)
    if requested not in EXPECTED:
        raise ValueError("Expected one of the eleven reviewed Mathlib rows")
    return (requested,)


def receipts(config):
    identity = runner.LAKE_LOCKS | {"protocol": 1, "helper_sha256": runner.DEPENDENCY_HELPER_SHA}
    good = {"status": "PASS", "proof_check_run": False, "identity": identity}
    return (
        "".join(root + "\n" for root in config["artifact_roots"]).encode("ascii"),
        dict(good, mode="sources", packages=[
            {"name": n, "rev": rev} for n, rev in runner.PACKAGE_REVISIONS.items()
        ]),
        dict(good, mode="artifacts", attempts=[{"label": "upstream-artifacts", "exit_code": 0}]),
    )


class MathlibIntakeTests(unittest.TestCase):
    def test_exact_modes_roots_and_stock_admission(self):
        self.assertEqual(set(runner.ALLOWLIST), set(EXPECTED) | {runner.CORE_PACKET})
        head = runner.git_at(runner.ROOT, "rev-parse", "HEAD").decode().strip()
        for packet in packets():
            config = runner.ALLOWLIST[packet]
            with self.subTest(packet=packet):
                with runner.admitted(runner.ROOT, head, packet, config) as (folder, data, audit):
                    self.assertEqual(data["order"], [n for n, _, _ in config["modules"]])
                    self.assertEqual(len(data["order"]), FRESH[packet])
                    self.assertEqual(len(config["artifact_roots"]), EXPECTED[packet])
                    self.assertEqual(set(p.name for p in folder.iterdir()),
                                     {"intake.json", *(n + ".lean" for n in data["order"])})
                    self.assertEqual(runner.digest(audit), config["audit_sha256"])
                    if packet in (CRT, TRACE):
                        module = {CRT: b"SelectedPELMarkingCRT318", TRACE: b"SelectedJOneCRTTrace318"}[packet]
                        self.assertEqual(audit.splitlines()[1:5], [
                            b"import all " + module,
                            b"public meta import Lean", b"public meta import Lean.Elab.Command",
                            b"public meta import Lean.Util.CollectAxioms",
                        ])
                    elif packet == TWIST:
                        self.assertEqual(data["order"], [
                            "CheckedHomogeneousTwistPoint318", "CheckedHomogeneousTwistPoint937Smoke318",
                        ])
                        self.assertEqual(config["source_paths"], {
                            "CheckedHomogeneousTwistPoint318": runner.INTAKES +
                            "/forward-detached-twist-point-r2/CheckedHomogeneousTwistPoint318.lean",
                        })
                        self.assertIn(b"public meta import Lean.Elab.Command", audit)
                    elif packet == REFLECT:
                        self.assertEqual(data["order"][-1], "Raw318InputReflection318")
                        self.assertIn(b"public meta import Lean.Elab.Command", audit)
                        self.assertFalse(config.get("source_paths"))
                        for name in data["order"][:-1]:
                            path = runner.PROGRESS + "/" + name + ".lean"
                            historical = runner.tree_entries(runner.ROOT, head, path)[path]
                            source = (folder / (name + ".lean")).read_bytes()
                            # Recompute Git's blob identity without fetching the original
                            # into this sparse worktree; no predecessor .olean is consulted.
                            self.assertEqual(historical, ("100644", "blob", hashlib.sha1(
                                b"blob " + str(len(source)).encode("ascii") + b"\x00" + source).hexdigest()))
                    elif packet == STRUCTURAL:
                        self.assertEqual(data["order"], ["SelectedJStructuralNormalization318"])
                        self.assertFalse(config.get("source_paths"))
                        self.assertIn(b"public meta import Lean.Elab.Command", audit)
                    else:
                        self.assertNotIn(b"import Lean.Elab.Command\n", audit)
                    if packet in (LENSTRA, CRT, TRACE):
                        self.assertFalse(config.get("source_paths"))
                        self.assertEqual(len(data["order"]), 1)
                    self.assertIn(b"collectAxioms name", audit)
                    if packet == DIFFERENT:
                        self.assertEqual(data["order"], [
                            "SelectedJOneDirectLenstraClear318", "SelectedJOneCRTTrace318",
                            "SelectedJOneCRTDifferent318",
                        ])
                        self.assertEqual(config["source_paths"], {
                            "SelectedJOneDirectLenstraClear318": runner.INTAKES + "/" + LENSTRA +
                                "/SelectedJOneDirectLenstraClear318.lean",
                            "SelectedJOneCRTTrace318": runner.INTAKES + "/" + TRACE +
                                "/SelectedJOneCRTTrace318.lean",
                        })
                    if packet == DYADIC:
                        self.assertEqual(data["order"][-2:], ["FractionDerivation318", "SelectedSameADyadicVerticalD2_318"])
                        donors = {n: runner.INTAKES + "/finite-height-dlog-rows-r4/" + n + ".lean"
                                  for n in data["order"][:3]}
                        donors["SelectedSameADyadicVerticalD2_318"] = (
                            runner.INTAKES + "/finite-plus11-dyadic-vertical-r1/SelectedSameADyadicVerticalD2_318.lean")
                        self.assertEqual(config["source_paths"], donors)
                        # The repaired copy differs from the historical progress blob by
                        # exactly one audited line; neither input is a project artifact.
                        src = runner.PROGRESS + "/FractionDerivation318.lean"
                        self.assertEqual(runner.tree_entries(runner.ROOT, head, src)[src],
                                         ("100644", "blob", "31e417380682bd958d1ce1be568831cc2899e96a"))
                        revised = (folder / "FractionDerivation318.lean").read_bytes()
                        prefix = b"  apply isUnit_iff_ne_zero.mpr\n"
                        good = prefix + b"  simp [jet]\n"
                        before = prefix + (b"  simpa [jet] using (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors "
                                  b"(S := K) s.property)\n")
                        self.assertEqual(revised.count(good), 1)
                        self.assertEqual(runner.digest(revised.replace(good, before, 1)),
                                         "79514f79cc4ff0bfc5a13b5a67214c838f3477f1a356b3eb71c380fdb6b67a42")
                    if packet == DLOG:
                        self.assertNotIn("packet", data)
                        self.assertEqual(set(config["source_paths"]), set(data["order"][:-1]))
                        owner = runner.INTAKES + "/finite-height-dlog-rows-r4/"
                        for module, path in config["source_paths"].items():
                            self.assertEqual(path, owner + module + ".lean")

    def test_two_native_scoped_matrix_fail_closed_elsewhere(self):
        # Parse the actual finite subset of GHA expressions emitted here; do
        # not infer a decision from the packet name or merely count strings.
        wf = (runner.ROOT / ".github/workflows/progress-standalone-intake.yml").read_text()
        cuts = re.findall(r"^          - packet: ([a-z][a-z0-9-]*)\n"
                          r"            profile: [^\n]+\n            root_count: [0-9]+\n"
                          r"            verification: (kernel check|>-\n(?: {14,}[^\n]+\n?)+)", wf, re.M)
        self.assertEqual([k for k, _ in cuts], list(runner.ALLOWLIST))
        base = 'e00436673024e42b0b26c2f205d3cfea43a04adb'
        newest = {REFLECT, OBSERVED}
        narrow = ("${{ github.event.before == '"+base+"' && join(github.event.commits.*.id, ',') "
                  "== github.sha && !github.event.forced && 'source admission only' || 'kernel check' }}")
        def rows(event_before, commits, head, forced):
            result = {}
            for key, raw in cuts:
                if raw == "kernel check":
                    self.assertIn(key, newest)
                    result[key] = "native"
                else:
                    self.assertNotIn(key, newest)
                    self.assertEqual(" ".join(raw.removeprefix(">-").split()), narrow)
                    reduced = event_before == base and ",".join(commits) == head and not forced
                    result[key] = "source" if reduced else "native"
            return result
        head = "f" * 40
        selected = rows(base, [head], head, False)
        self.assertEqual({k for k, v in selected.items() if v == "native"}, newest)
        self.assertEqual(list(selected.values()).count("source"), 10)
        for ev in [("a"*40, [head], False), (base, [], False),
                   (base, ["a"*40, head], False), (base, [head], True), (None, [], False)]:
            self.assertEqual(set(rows(ev[0], ev[1], head, ev[2]).values()), {"native"})

    def test_static_external_donors_are_canonical_and_named(self):
        config = runner.ALLOWLIST[GRAM]
        files = runner.source_paths(GRAM, config)
        self.assertEqual(len(config["source_paths"]), 2)
        for name, source in config["source_paths"].items():
            self.assertEqual(files[name + ".lean"], source)
            for wrong in (source.replace("/intake/", "/intake/../intake/"), source + "/../",
                          source.replace(name + ".lean", "NotTheDonor.lean"), source[1:]):
                broken = deepcopy(config)
                broken["source_paths"][name] = wrong
                with self.subTest(wrong=wrong), self.assertRaisesRegex(ValueError, "donor path"):
                    runner.source_paths(GRAM, broken)
        broken = deepcopy(config)
        broken["source_paths"]["Unlisted"] = "arbitrary.lean"
        with self.assertRaisesRegex(ValueError, "unlisted module"):
            runner.source_paths(GRAM, broken)

    def test_mismatched_roots_rejected(self):
        cfg = runner.ALLOWLIST[DLOG]
        with self.assertRaisesRegex(ValueError, "differ from admitted"):
            runner.profile_contract({**cfg, "artifact_roots": cfg["artifact_roots"][:-1]})
        with self.assertRaisesRegex(ValueError, "sorted unique"):
            runner.profile_contract({**cfg, "source_roots": (*cfg["source_roots"], cfg["source_roots"][-1])})

    def test_receipt_stage_and_exact_targets(self):
        for packet in packets():
            cfg = runner.ALLOWLIST[packet]
            targets, sources, artifacts = receipts(cfg)
            runner.validate_setup_receipts(cfg, targets, sources, artifacts)
            for bad_targets in (targets + b"Mathlib\n", b""):
                with self.assertRaisesRegex(ValueError, "target file differs"):
                    runner.validate_setup_receipts(cfg, bad_targets, sources, artifacts)
            for key, value in (("status", "FAIL"), ("mode", "sources"),
                               ("proof_check_run", True), ("identity", {})):
                with self.assertRaisesRegex(ValueError, "setup receipt"):
                    runner.validate_setup_receipts(cfg, targets, sources, {**artifacts, key: value})
            with self.assertRaisesRegex(ValueError, "package revisions"):
                runner.validate_setup_receipts(cfg, targets, {**sources, "packages": []}, artifacts)
            with self.assertRaisesRegex(ValueError, "No successful"):
                runner.validate_setup_receipts(cfg, targets, sources, {**artifacts, "attempts": []})

    def test_only_fresh_and_locked_libraries_pass_to_native_environment(self):
        packet = packets()[0]
        cfg = runner.ALLOWLIST[packet]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            project = root / runner.PROGRESS
            project.mkdir(parents=True)
            for name in runner.LAKE_LOCKS:
                (project / name).write_bytes((runner.ROOT / runner.PROGRESS / name).read_bytes())
            lock = json.loads((project / "lake-manifest.json").read_bytes())
            fake_rows = {p["name"]: p for p in lock["packages"]}
            setup = root / runner.DEP_OUTPUT
            setup.mkdir(parents=True)
            targets, sources, artifacts = receipts(cfg)
            (setup / (packet + ".targets.txt")).write_bytes(targets)
            (setup / "sources.json").write_text(json.dumps(sources))
            (setup / (packet + ".artifacts.json")).write_text(json.dumps(artifacts))
            packages = project / ".lake/packages"
            for p in fake_rows:
                (packages / p / ".git").mkdir(parents=True)
            mathlib = packages / "mathlib/.lake/build/lib/lean"
            for r in cfg["artifact_roots"]:
                target = mathlib / (r.replace(".", "/") + ".olean")
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(b"fixture-only, never a real Lean input")
            progress_lib = project / ".lake/build/lib/lean"
            progress_lib.mkdir(parents=True)
            fresh = root / "fresh"

            def git_fixture(path, *args):
                self.assertEqual(path.parent, packages)
                p = fake_rows[path.name]
                if args == ("rev-parse", "HEAD"):
                    return (p["rev"] + "\n").encode()
                if args == ("remote", "get-url", "origin"):
                    return (p["url"] + "\n").encode()
                self.assertEqual(args, ("diff", "--quiet", "HEAD", "--"))
                return b""

            with patch.object(runner, "git_at", side_effect=git_fixture):
                libs, receipt = runner.mathlib_setup(root, packet, cfg)
                self.assertEqual(libs, (mathlib,))
                self.assertEqual(receipt["dependency_revisions"], runner.PACKAGE_REVISIONS)
                env = runner.profile_environment(cfg, fresh, {"LEAN_PATH": str(progress_lib)}, libs)
                self.assertEqual(env["LEAN_PATH"].split(os.pathsep), [str(fresh), str(mathlib)])
                target.unlink()
                with self.assertRaisesRegex(ValueError, "Missing pinned upstream artifact"):
                    runner.mathlib_setup(root, packet, cfg)


if __name__ == "__main__":
    unittest.main()
