#!/usr/bin/env python3
"""Source/invocation fixtures; never execute Lean, Lake, or install packages."""
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

import check_standalone_intake as runner


class IntakeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.head = runner.git_at(runner.ROOT, "rev-parse", "HEAD").decode().strip()
        cls.packet = runner.CORE_PACKET
        cls.config = runner.ALLOWLIST[cls.packet]
        cls.payload = runner.read_payload(runner.ROOT, cls.head, cls.packet, cls.config)
        cls.source = runner.CORE_MODULE + ".lean"

    def test_reviewed_stock_admission(self):
        with runner.admitted(runner.ROOT, self.head, self.packet, self.config) as (p, d, a):
            self.assertEqual(d["order"], [runner.CORE_MODULE])
            self.assertEqual(d["packet"], "weighted-readback-core")
            self.assertNotEqual(d["packet"], p.name)
            self.assertEqual(runner.digest(a), self.config["audit_sha256"])
            self.assertIn(b"import all " + runner.CORE_MODULE.encode(), a)
            self.assertIn(b"collectAxioms name", a)
            self.assertEqual(tuple(self.config["artifact_roots"]), ())

    def test_rehashed_source_and_manifest_rejected(self):
        p = dict(self.payload)
        d = json.loads(p["intake.json"])
        p[self.source] += b"\n-- changed consumer without changed imports\n"
        d["files"][self.source]["sha256"] = runner.digest(p[self.source])
        p["intake.json"] = (json.dumps(d) + "\n").encode()
        with self.assertRaisesRegex(ValueError, "Changed exact intake manifest"):
            runner.validate_payload(self.config, p)

    def test_raw_tampering_and_extra_source_rejected(self):
        p = dict(self.payload)
        p[self.source] += b"\n"
        with self.assertRaisesRegex(ValueError, "Changed exact source"):
            runner.validate_payload(self.config, p)
        p["Sibling.lean"] = b""
        with self.assertRaisesRegex(ValueError, "Payload names"):
            runner.validate_payload(self.config, p)

    def test_audit_codegen_drift_rejected(self):
        cfg = deepcopy(self.config)
        cfg["audit_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "Changed private recursive audit"):
            with runner.admitted(runner.ROOT, self.head, self.packet, cfg):
                self.fail("Audit drift did not stop admission")

    def test_unsupported_profile_and_wrong_profile_roots_rejected(self):
        with self.assertRaisesRegex(ValueError, "Unimplemented runner profile"):
            runner.profile_contract({**self.config, "profile": "pinned-mathlib"})
        with self.assertRaisesRegex(ValueError, "may not fetch"):
            runner.profile_contract({**self.config, "artifact_roots": ("Mathlib.Tactic",)})
        with self.assertRaisesRegex(ValueError, "Non-core root"):
            runner.profile_contract({**self.config, "source_roots": ("Mathlib.Tactic",)})

    def test_compiler_environment_does_not_inherit_paths(self):
        fresh = Path("/scratch/new/core-lib")
        environ = dict(PATH="/usr/bin", LEAN_PATH="untrusted", LEAN_SRC_PATH="untrusted",
                       LEAN_SYSROOT="untrusted", LAKE_HOME="untrusted", LD_PRELOAD="untrusted")
        self.assertEqual(runner.profile_environment(self.config, fresh, environ),
                         dict(PATH="/usr/bin", LEAN_PATH=str(fresh)))

    def test_audit_marker_requires_exact_count_and_success(self):
        marker = "info: EXPERIMENT_AUDIT_PASS declarations=5 modules=1\n"
        self.assertEqual(runner.audit_count(marker, 1), 5)
        for bad in ("", marker + marker, marker.replace("modules=1", "modules=2"),
                    marker.replace("declarations=5", "declarations=0")):
            with self.subTest(bad=bad), self.assertRaisesRegex(ValueError, "Incomplete"):
                runner.audit_count(bad, 1)

    def test_exact_hosted_identity(self):
        valid = {
            "GITHUB_ACTIONS": "true", "GITHUB_EVENT_NAME": "push", "GITHUB_REF": runner.BRANCH,
            "RUNNER_OS": "Linux", "RUNNER_ARCH": "X64", "ImageOS": "ubuntu24",
            "GITHUB_SHA": self.head,
        }
        commit, tree = runner.hosted_identity(runner.ROOT, valid)
        self.assertEqual(commit, self.head)
        self.assertRegex(tree, r"^[0-9a-f]{40}$")
        for key, value in (("GITHUB_SHA", "0"*40), ("GITHUB_REF", "refs/heads/main"),
                           ("GITHUB_EVENT_NAME", "pull_request"), ("RUNNER_ARCH", "ARM64")):
            with self.subTest(key=key), self.assertRaises(ValueError):
                runner.hosted_identity(runner.ROOT, {**valid, key: value})

    def test_tracked_symlink_and_unlisted_file_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            git = ["git", "-C", tmp]
            def run(*args):
                subprocess.run([*git, *args], check=True, capture_output=True)
            run("init", "-q")
            run("config", "user.email", "fixture@example.invalid")
            run("config", "user.name", "Local fixture")
            run("config", "commit.gpgsign", "false")
            run("config", "core.hooksPath", "/dev/null")
            root = Path(tmp)
            folder = root / runner.INTAKES / self.packet
            folder.mkdir(parents=True)
            (folder / "intake.json").write_bytes(self.payload["intake.json"])
            (folder / self.source).symlink_to("intake.json")
            run("add", ".")
            run("commit", "-m", "Local symlink fixture")
            at = runner.git_at(root, "rev-parse", "HEAD").decode().strip()
            with self.assertRaisesRegex(ValueError, "Not a regular source blob"):
                runner.read_payload(root, at, self.packet, self.config)
            (folder / "Unlisted.lean").write_bytes(b"")
            run("add", ".")
            run("commit", "-m", "Local extra source fixture")
            at = runner.git_at(root, "rev-parse", "HEAD").decode().strip()
            with self.assertRaisesRegex(ValueError, "filenames differ"):
                runner.read_payload(root, at, self.packet, self.config)


if __name__ == "__main__":
    unittest.main()
