"""Pure text/guard tests. Never invokes Lean or a profiler."""
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import diagnose_original_endpoint as d

class EndpointDiagnosticTests(unittest.TestCase):
    def source(self):
        p=d.ci.ROOT/'quartics/quartic-318-326/proof/experiments'/d.PACKET/'OriginalGeometricEdge318.lean'
        return p.read_text()
    def test_source_is_exact_and_all_variants_are_scratch(self):
        source=self.source()
        import hashlib
        self.assertEqual(hashlib.sha256(source.encode()).hexdigest(),d.SOURCE_SHA)
        variants=d.variants(source)
        self.assertEqual(len(variants),6)
        for name,text in variants.items():
            self.assertIn('scratch_profile_sentinel',text)
            self.assertIn('set_option profiler.threshold 0',text)
            self.assertNotIn('lemma edge_to_module',text)
            self.assertEqual('sorry' in text,name.endswith('_sorry'))
        original=source.split('private lemma endpoint_square',1)[1].split('\nrun_cmd ',1)[0].rstrip()
        self.assertIn('private lemma endpoint_square'+original,variants['original_simpa'])
        self.assertNotIn('endpoint_square',variants['prefix_capture'])
    def test_main_refuses_local_execution_before_environment_access(self):
        with patch.dict(os.environ,{},clear=True), patch('sys.argv',['diag','--packet',d.PACKET]), \
                patch.object(d.ci,'environment') as env:
            with self.assertRaisesRegex(RuntimeError,'only on hosted'):
                d.main()
            env.assert_not_called()
    def test_workflow_does_not_admit_scratch_or_upload_oleans(self):
        text=(d.ci.ROOT/'.github/workflows/progress-experiments.yml').read_text()
        self.assertIn("if: always() && matrix.packet == 'contact-relative-site-descent-r26'",text)
        self.assertNotIn('/lib/',text)
        self.assertIn('scratch-diagnostics/',text)
        script=Path(d.__file__).read_text()
        self.assertNotIn("'-o'",script)
        self.assertIn("dir=os.environ['RUNNER_TEMP']",script)
        self.assertIn("'proof_acceptance': False",script)

if __name__=='__main__':unittest.main()
