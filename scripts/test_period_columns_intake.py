#!/usr/bin/env python3
"""Source/manifest fixtures for the isolated two-module period intake."""
from hashlib import sha256
import json
from pathlib import Path
import re
import tempfile
import unittest

import check_period_columns_intake as period
import check_progress_experiment as experiment


class PeriodIntakeTests(unittest.TestCase):
    def setUp(self):
        self.addCleanup((temp := tempfile.TemporaryDirectory()).cleanup)
        self.root = Path(temp.name)
        self.intake = self.root / period.INTAKE
        self.intake.mkdir(parents=True)
        manifest, bodies = period.read_packet()
        (self.intake / "intake.json").write_bytes(manifest)
        for name, data in bodies.items():
            (self.intake / name).write_bytes(data)

    def manifest(self, change):
        p = self.intake / "intake.json"
        data = json.loads(p.read_bytes())
        change(data)
        p.write_text(json.dumps(data) + "\n", encoding="utf-8")

    def test_exact_order_upstream_and_unchanged_private_audit(self):
        with period.admitted_packet(self.root) as (_, data, actual):
            self.assertEqual(data["order"], list(period.EXPECTED))
            self.assertEqual(len(actual), 7)
            self.assertEqual(set(actual), set().union(*period.EXPECTED.values()) - set(period.EXPECTED))
            audit = experiment.audit_text(data["order"])
            imports = re.findall(r"^import all (\w+)$", audit, re.MULTILINE)
            self.assertEqual(imports, list(period.EXPECTED))
            self.assertIn("collectAxioms name", audit)
            self.assertIn("env.header.moduleData[idx]!.constNames", audit)
            self.assertEqual(sha256(audit.encode()).hexdigest(),
                "da8730ac2b88e49a31485bd54c744391568c49e377567ec3691adff77b7e01c8")

    def test_tampered_consumer_rejected(self):
        p = self.intake / "SelectedActualPELPeriodColumns318.lean"
        p.write_bytes(p.read_bytes() + b"\n-- unexpected edit\n")
        with self.assertRaisesRegex(ValueError, "Period source hash mismatch"):
            period.read_packet(self.root)

    def test_rehashed_alternate_donor_rejected(self):
        p = self.intake / "QuaternionicRealPeriod318.lean"
        raw = p.read_bytes() + b"\n-- alternate donor\n"
        p.write_bytes(raw)
        self.manifest(lambda d: d["files"][p.name].update(sha256=sha256(raw).hexdigest()))
        with self.assertRaisesRegex(ValueError, "Unexpected corrected period donor"):
            period.read_packet(self.root)

    def test_order_rejected(self):
        self.manifest(lambda d: d["order"].reverse())
        with self.assertRaisesRegex(ValueError, "Unexpected period module order"):
            period.read_packet(self.root)

    def test_wrong_source_pin_rejected(self):
        self.manifest(lambda d: d.update(source_pin="0" * 40))
        with self.assertRaisesRegex(ValueError, "Unexpected period packet or source pin"):
            period.read_packet(self.root)

    def test_rehashed_import_drift_rejected(self):
        p = self.intake / "SelectedActualPELPeriodColumns318.lean"
        raw = p.read_bytes().replace(b"public import QuaternionicRealPeriod318",
                                     b"public import ContactGlobalBicanonical318", 1)
        self.assertNotEqual(raw, p.read_bytes())
        p.write_bytes(raw)
        self.manifest(lambda d: d["files"][p.name].update(sha256=sha256(raw).hexdigest()))
        with self.assertRaisesRegex(ValueError, "Declared imports mismatch"):
            with period.admitted_packet(self.root):
                pass


if __name__ == "__main__":
    unittest.main()
