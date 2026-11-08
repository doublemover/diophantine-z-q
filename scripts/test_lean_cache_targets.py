"""Dependency-root selection must fail closed and retain all real imports."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from lean_cache_targets import cache_targets, imports


class CacheTargetsTests(unittest.TestCase):
    def test_import_syntax_and_comments(self):
        text = '''module
public import all Mathlib.A
import Mathlib.B Mathlib.C -- import Bad.Comment
/- import Bad.Nested /- another -/ -/
meta import Lean.Elab.Tactic
def example := "import Bad.String"
'''
        self.assertEqual(imports(text),
                         {"Mathlib.A", "Mathlib.B", "Mathlib.C", "Lean.Elab.Tactic"})

    def test_manifest_binding_and_root_audit_imports(self):
        with tempfile.TemporaryDirectory() as temp:
            project = Path(temp)
            (project / "ZInQ").mkdir()
            (project / "Checks").mkdir()
            source = project / "ZInQ/Test.lean"
            source.write_text("import Mathlib.A\nimport Lean.Elab.Tactic\n")
            (project / "ZInQ.lean").write_text("public import ZInQ.Test\n")
            (project / "Checks/Axioms.lean").write_text(
                "import all ZInQ\nimport Mathlib.B\nimport Lean.Util.CollectAxioms\n")
            (project / "SOURCE_MANIFEST.json").write_text(json.dumps({"files": [{
                "module": "ZInQ.Test", "path": "ZInQ/Test.lean",
                "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            }]}))
            self.assertEqual(cache_targets(project), ["Mathlib.A", "Mathlib.B"])
            source.write_text("import Mathlib.Changed\n")
            with self.assertRaisesRegex(ValueError, "manifest mismatch"):
                cache_targets(project)


if __name__ == "__main__":
    unittest.main()
