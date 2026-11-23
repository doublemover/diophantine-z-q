#!/usr/bin/env python3
"""Offline shadow controls; none of these assertions is a native Lean receipt."""
from pathlib import Path
import subprocess
import tempfile
import unittest

import standalone_shadow as sh

REG = sh.stock.ALLOWLIST
ORDER = tuple(REG)
TRACE = "same-j-crt-trace-r2"
DIFF = "same-j-crt-different-r1"
OWN = sh.owners(REG)
DONOR = next(p for p, ids in OWN.items() if p.endswith("SelectedJOneCRTTrace318.lean") and len(ids) > 1)


class Decisions(unittest.TestCase):
    def test_matrix_root_count_drift(self):
        data = (sh.stock.ROOT / sh.WORKFLOW).read_text()
        sh.matrix_shape(data, REG)
        with self.assertRaisesRegex(ValueError, "root count"):
            sh.matrix_shape(data.replace("root_count: 10", "root_count: 7"), REG)

    def test_true_shared_donor(self):
        rules, full = sh.classify(ORDER, OWN, [("M", DONOR)])
        self.assertFalse(full)
        self.assertEqual({p for p, paths in rules.items() if paths}, {TRACE, DIFF})

    def test_all_graph_shape_changes(self):
        for kind in ("R100", "A", "D", "T", "C100"):
            self.assertTrue(sh.classify(ORDER, OWN, [(kind, DONOR)])[1])

    def test_global_controls_and_unknown_fail_full(self):
        for name in (sh.RUNNER, sh.WORKFLOW, ".github/actions/setup-pinned-lean/action.yml",
                     "lean/lean-toolchain", "unknown", "scripts/standalone_shadow.py"):
            self.assertTrue(sh.classify(ORDER, OWN, [("M", name)])[1])

    def test_inert_no_native_evidence(self):
        affected, full = sh.classify(ORDER, OWN, [("M", "README.md")])
        self.assertFalse(full)
        self.assertFalse(any(affected.values()))

    def test_nul_parser_not_whitespace_parser(self):
        self.assertEqual(sh.diff_entries(b"M\0odd\nname\0"), [("M", "odd\nname")])
        for malformed in (b"M\0path", b"M\0", b"M\0\xff\0"):
            with self.assertRaises(ValueError):
                sh.diff_entries(malformed)

    def test_event_not_push_or_wrong_head_never_narrows(self):
        a, b = "a"*40, "b"*40
        event = dict(before=a, after=b, ref=sh.stock.BRANCH, repository={"full_name":
                     "doublemover/diophantine-z-q"}, created=False, deleted=False, forced=False)
        sh.verify_push(event, a, b)
        for patch_ in ({"before": b}, {"after": a}, {"ref": "refs/heads/main"},
                       {"forced": True}, {"created": True}, {"deleted": True},
                       {"repository": {"full_name": "other/name"}}):
            with self.assertRaises(ValueError):
                sh.verify_push(event | patch_, a, b)


class ActualGitDiff(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.git("init", "-q")
        self.git("config", "user.name", "fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        self.write(sh.RUNNER, Path(sh.stock.__file__).read_bytes())
        self.write(sh.WORKFLOW, ("\n".join(f"          - packet: {p}\n            profile: {c['profile']}\n"
                                    f"            root_count: {len(c['artifact_roots'])}" for p, c in REG.items()) + "\n").encode())
        self.write("README.md", b"base")
        self.write(DONOR, b"source fixture")
        self.base = self.save("base")

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.root), *args]).decode().strip()

    def write(self, path, val):
        p = self.root / path
        p.parent.mkdir(exist_ok=True, parents=True)
        p.write_bytes(val)

    def save(self, msg):
        self.git("add", ".")
        self.git("commit", "-q", "-m", msg)
        return self.git("rev-parse", "HEAD")

    def test_multicommit_catches_earlier_donor_and_orders_result(self):
        self.write(DONOR, b"revised donor")
        self.save("changed true input")
        self.write("README.md", b"later doc")
        head = self.save("doc")
        out = sh.shadow(self.root, self.base, head)
        self.assertFalse(out["fallback_all"])
        self.assertEqual(out["change_count"], 2)
        self.assertEqual([r["packet"] for r in out["rows"] if r["recommended"] == "native"], [TRACE, DIFF])
        self.assertTrue(all(not r["verified"] for r in out["rows"]))

    def test_registry_disagreement_or_missing_sha_fail_closed(self):
        self.write(sh.WORKFLOW, b"          - packet: new-row\n")
        head = self.save("unsupported workflow")
        for before, after in [(self.base, head), (self.base, self.base), ("0"*40, head), ("--help", head)]:
            out = sh.shadow(self.root, before, after)
            self.assertTrue(out["fallback_all"])
            self.assertTrue(all(r["recommended"] == "native" for r in out["rows"]))

    def test_actual_rename_and_unrelated_history_fail_closed(self):
        (self.root / DONOR).rename(self.root / "moved-source")
        head = self.save("moved")
        out = sh.shadow(self.root, self.base, head)
        self.assertTrue(out["fallback_all"])
        self.git("checkout", "-q", "--orphan", "separate")
        self.write("README.md", b"other history")
        other = self.save("new root")
        self.assertTrue(sh.shadow(self.root, head, other)["fallback_all"])

    def test_source_only_aggregate_guards_head(self):
        with self.assertRaisesRegex(ValueError, "runner and checkout differ"):
            sh.aggregate(self.root, self.base)


if __name__ == "__main__":
    unittest.main()
