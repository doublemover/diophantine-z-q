#!/usr/bin/env python3
"""Source admission negative controls. No Lean, Git, cache or network."""

import hashlib
import json
from pathlib import Path
import tempfile
import unittest

import check_affine_collision_intake as intake


class AffineCollisionIntakeTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.manifest = self.root / intake.INTAKE / "intake.json"
        self.data = {"order": list(intake.EXPECTED), "files": {}}
        for name, imports in intake.EXPECTED.items():
            source = self.root / intake.source_path(name)
            source.parent.mkdir(parents=True, exist_ok=True)
            raw = ("module\n" + "".join(f"public import {x}\n" for x in sorted(imports)) +
                   "\npublic section\ntheorem sample : True := True.intro\n").encode()
            source.write_bytes(raw)
            self.data["files"][source.name] = {
                "imports": sorted(imports), "sha256": hashlib.sha256(raw).hexdigest()
            }
        self.write_manifest()

    def write_manifest(self):
        self.manifest.write_text(json.dumps(self.data), encoding="utf-8")

    def add_rehashed_code(self, module, extra):
        source = self.root / intake.source_path(module)
        raw = source.read_bytes() + extra
        source.write_bytes(raw)
        self.data["files"][source.name]["sha256"] = hashlib.sha256(raw).hexdigest()
        self.write_manifest()

    def test_admits_exact_closure_with_no_project_predecessors(self):
        with intake.admitted_packet(self.root) as (folder, data, roots):
            self.assertEqual(data["order"], list(intake.EXPECTED))
            self.assertEqual(roots, [
                "Mathlib.Algebra.Field.ZMod",
                "Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic",
                "Mathlib.Tactic",
            ])
            self.assertNotEqual(folder.parent, self.root)
            for name in data["order"]:
                self.assertEqual((folder / (name + ".lean")).read_bytes(),
                                 (self.root / intake.source_path(name)).read_bytes())

    def test_rejects_stale_donor_bytes(self):
        source = self.root / intake.source_path("LinearA4GaussianCounts318")
        source.write_bytes(source.read_bytes() + b"\n")
        with self.assertRaisesRegex(ValueError, "Affine source hash mismatch"):
            intake.read_packet(self.root)

    def test_rejects_missing_or_reordered_donor(self):
        self.data["order"].reverse()
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "Unexpected affine module order"):
            intake.read_packet(self.root)

    def test_rejects_rehashed_unlisted_import(self):
        self.add_rehashed_code("LinearA4CollisionBins318", b"\nimport UncheckedLocalDonor\n")
        with self.assertRaisesRegex(ValueError, "Declared imports mismatch"):
            with intake.admitted_packet(self.root):
                self.fail("admitted unexpectedly")

    def test_rejects_even_manifest_claimed_extra_import(self):
        files = self.data["files"]
        files["LinearA4CollisionBins318.lean"]["imports"].append("Mathlib")
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "Unexpected declared imports"):
            intake.read_packet(self.root)

    def test_rejects_rehashed_kernel_escape(self):
        self.add_rehashed_code("LinearA4CollisionBins318", b"\nexample : False := by sorry\n")
        with self.assertRaisesRegex(ValueError, "Unproved axiom, placeholder"):
            with intake.admitted_packet(self.root):
                self.fail("admitted unexpectedly")


if __name__ == "__main__":
    unittest.main()
