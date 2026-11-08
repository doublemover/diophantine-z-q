"""Regression tests for dependency invalidation and artifact admission."""
import argparse
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check_progress_lean as ci


class ProgressTests(unittest.TestCase):
    def fixture(self, root):
        root.mkdir(exist_ok=True)
        (root / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
        (root / "lake-manifest.json").write_text('{"packages": []}\n')
        sources = {"A": "module\npublic def a : Nat := 1\n",
                   "B": "module\npublic import A\npublic def b : Nat := a\n",
                   "C": "module\npublic def c : Nat := 2\n"}
        for name, text in sources.items(): (root / (name + ".lean")).write_text(text)
        (root / "CheckpointAudit.lean").write_text("module\nimport all A\nimport all B\nimport all C\n")
        self.manifest(root, list(sources))

    def manifest(self, root, order):
        ci.write_json(root / "module-order.json", order)
        ci.write_json(root / "checkpoint-manifest.json", {
            "module_order": order,
            "modules": {n: {"sha256": ci.sha(root / (n + ".lean"))} for n in order}})

    def test_dependency_invalidation_is_transitive_and_selective(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); self.fixture(root)
            before = ci.derive_plan(root, 2)
            (root / "A.lean").write_text("module\npublic def a : Nat := 3\n")
            self.manifest(root, ["A", "B", "C"])
            after = ci.derive_plan(root, 2)
            self.assertNotEqual(before["module_keys"]["A"], after["module_keys"]["A"])
            self.assertNotEqual(before["module_keys"]["B"], after["module_keys"]["B"])
            self.assertEqual(before["module_keys"]["C"], after["module_keys"]["C"])
            self.assertEqual(before["base"], after["base"])
            (root / "lean-toolchain").write_text("changed toolchain\n")
            changed = ci.derive_plan(root, 2)
            self.assertNotEqual(after["module_keys"]["C"], changed["module_keys"]["C"])

    def test_source_hash_and_audit_coverage_fail_closed(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); self.fixture(root)
            (root / "A.lean").write_text("changed")
            with self.assertRaisesRegex(ValueError, "Source hash"):
                ci.derive_plan(root)
            self.fixture(root)
            (root / "CheckpointAudit.lean").write_text("import A\n")
            with self.assertRaisesRegex(ValueError, "every snapshot module"):
                ci.derive_plan(root)

    def test_cohorts_cover_every_module_and_its_dependencies(self):
        plan = ci.derive_plan()
        all_modules = set()
        for group in plan["cohorts"]:
            seen = set(group["imports"])
            self.assertTrue(all(plan["depth"][n] < plan["split_depth"] for n in seen))
            for name in group["modules"]:
                self.assertTrue(set(plan["dependencies"][name]).issubset(seen))
                seen.add(name)
            all_modules.update(seen)
        self.assertEqual(all_modules, set(plan["module_order"]))

    def test_replay_order_must_match_authoritative_manifest(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); self.fixture(root)
            ci.write_json(root / "module-order.json", ["A", "C"])
            with self.assertRaisesRegex(ValueError, "authoritative manifest"):
                ci.derive_plan(root)

    def test_cache_checks_bytes_and_actual_dependency_artifacts(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); self.fixture(root)
            plan = ci.derive_plan(root)
            lib = root / "lib"; lib.mkdir()
            (lib / "B.olean").write_bytes(b"artifact")
            built = {"A": {"files": {".olean": "dependency-hash"}}}
            entry = {"key": plan["module_keys"]["B"], "files": ci.artifact_hashes(lib, "B"),
                     "dependency_artifacts": {"A": built["A"]["files"]}}
            self.assertTrue(ci.reusable(entry, "B", plan, lib, built))
            changed = {"A": {"files": {".olean": "different"}}}
            self.assertFalse(ci.reusable(entry, "B", plan, lib, changed))
            (lib / "B.olean").write_bytes(b"corruption")
            self.assertFalse(ci.reusable(entry, "B", plan, lib, built))

    def test_clean_build_does_not_reuse_valid_cache(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "project"; self.fixture(root)
            plan = ci.derive_plan(root, 1)
            cache = Path(temp) / "cache"
            def fake_compile(project, env, label, source, target, logs, root=None):
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(source.read_bytes())
                return {"module": label, "exit_code": 0, "seconds": 0}
            with patch.object(ci, "PROJECT", root), \
                 patch.object(ci, "environment", return_value=({}, "test")), \
                 patch.object(ci, "ensure_official"), \
                 patch.object(ci, "compile_one", side_effect=fake_compile) as compiler:
                args = argparse.Namespace(cohort=0, cache=cache, clean=False,
                                          output=Path(temp) / "first")
                ci.build_cohort(args, plan)
                self.assertEqual(compiler.call_count, 3)
                compiler.reset_mock(); args.output = Path(temp) / "cached"
                ci.build_cohort(args, plan)
                self.assertEqual(compiler.call_count, 0)
                self.assertEqual(len(json.loads((args.output / "receipt.json").read_text())["reused"]), 3)
                compiler.reset_mock(); args.output = Path(temp) / "clean"; args.clean = True
                ci.build_cohort(args, plan)
                self.assertEqual(compiler.call_count, 3)
                self.assertEqual(json.loads((args.output / "receipt.json").read_text())["reused"], [])

    def test_cross_stage_artifacts_are_verified_not_rebuilt_or_reuploaded(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "project"; self.fixture(root)
            plan = ci.derive_plan(root, 2, split_depth=1)
            bundles = Path(temp) / "bundles"; bundles.mkdir()
            def fake_compile(project, env, label, source, target, logs, root=None):
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(source.read_bytes())
                return {"module": label, "exit_code": 0, "seconds": 0}
            with patch.object(ci, "PROJECT", root), \
                 patch.object(ci, "environment", return_value=({}, "test")), \
                 patch.object(ci, "ensure_official"), \
                 patch.object(ci, "compile_one", side_effect=fake_compile) as compiler:
                for cohort in plan["cohorts"]:
                    args = argparse.Namespace(cohort=cohort["id"], clean=False, bundles=bundles,
                        cache=Path(temp) / f"cache-{cohort['id']}",
                        output=bundles / f"progress-cohort-{cohort['id']}")
                    ci.build_cohort(args, plan)
                    for name in cohort["imports"]:
                        self.assertFalse((args.output / "lib" / (name + ".olean")).exists())
                self.assertEqual(compiler.call_count, 3)
            entries, _, _, _, _ = ci.collect_bundles(bundles, plan, plan["cohorts"])
            self.assertEqual(set(entries), {"A", "B", "C"})
            foundation = next(c for c in plan["cohorts"] if "A" in c["modules"])
            (bundles / f"progress-cohort-{foundation['id']}" / "lib/A.olean").write_bytes(b"corrupt")
            with self.assertRaisesRegex(ValueError, "Corrupt cohort"):
                ci.collect_bundles(bundles, plan, plan["cohorts"])


if __name__ == "__main__": unittest.main()
