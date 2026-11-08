"""Cheap regressions for audit headers and reviewed-document carry-forward."""
from pathlib import Path
import importlib.util
import shutil
import tempfile
import unittest
import check_quartic_consumer_bindings as bindings

ROOT = Path(__file__).resolve().parents[1]
path = ROOT / 'quartics/quartic-318-326/proof/progress/verify_manifest.py'
spec = importlib.util.spec_from_file_location('manifest_check', path)
manifest = importlib.util.module_from_spec(spec)
spec.loader.exec_module(manifest)

class IntegrationTests(unittest.TestCase):
    def test_audit_requires_leading_module_and_private_imports(self):
        valid = 'module\nimport all A\nimport all B\nimport Lean.Util.CollectAxioms\nlet modules : Array Name := #[`A,`B]\n'
        manifest.validate_audit(valid, ['A', 'B'])
        for bad in [valid.replace('module\n', '') + 'module\n',
                    valid.replace('import all A', 'import A'),
                    valid.replace('#[`A,`B]', '#[`A]'),
                    valid.replace('#[`A,`B]', '#[`B,`A]'),
                    'import C\n' + valid]:
            with self.assertRaises(AssertionError):
                manifest.validate_audit(bad, ['A', 'B'])

    def test_current_binding_and_negative_controls(self):
        bindings.verify(ROOT)
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            for version in ['v11', 'v13']:
                rel = Path('docs/quartic-318-326') / (version + '-consumer-binding')
                shutil.copytree(ROOT / rel, root / rel)
            for rel in ['quartics/quartic-318-326/docs/arithmetic.md',
                        'quartics/quartic-318-326/proof/components/arithmetic-obligations.md',
                        'quartics/quartic-318-326/proof/components/verification.json']:
                target = root / rel; target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / rel, target)
            bindings.verify(root)
            targets = ['quartics/quartic-318-326/proof/components/arithmetic-obligations.md',
                       'quartics/quartic-318-326/docs/arithmetic.md',
                       'docs/quartic-318-326/v13-consumer-binding/decisions/group/acceptance.json',
                       'docs/quartic-318-326/v11-consumer-binding/arithmetic-obligations.before.md',
                       'docs/quartic-318-326/v13-consumer-binding/APPLICATION.json']
            for rel in targets:
                p = root / rel; original = p.read_bytes()
                p.write_bytes(original + b'changed\n')
                with self.assertRaises(AssertionError, msg=rel): bindings.verify(root)
                p.write_bytes(original)

if __name__ == '__main__': unittest.main()
