"""Pure source split and hosted-guard tests. Never runs Lean."""
import hashlib
import os
from pathlib import Path
import unittest
from unittest.mock import patch
import diagnose_candidate_endpoint as d

class CandidateEndpointDiagnosticTests(unittest.TestCase):
    def source(self):
        return (d.ci.ROOT/'quartics/quartic-318-326/proof/experiments'/d.PACKET/
                'OriginalGeometricEdge318.lean').read_text()

    def test_exact_no_sorry_endpoint_copy(self):
        source = self.source()
        self.assertEqual(hashlib.sha256(source.encode()).hexdigest(), d.SOURCE_SHA)
        variants = d.variants(source)
        self.assertEqual(set(variants), {'candidate_endpoint_only', 'candidate_edge_profile10k'})
        exact = source.split('private lemma endpoint_square', 1)[1].split('\nrun_cmd ', 1)[0]
        for text in variants.values():
            self.assertIn('private lemma endpoint_square'+exact, text)
            self.assertIn('set_option profiler.threshold 0', text)
            self.assertNotIn('sorry', text)
            self.assertIn('private lemma associate_endpoint', text)
        self.assertNotIn('edge_to_module', variants['candidate_endpoint_only'])
        edge = source.split('lemma edge_to_module', 1)[1].split('\nrun_cmd ', 1)[0]
        self.assertIn('lemma edge_to_module'+edge, variants['candidate_edge_profile10k'])

    def test_refuses_local_execution_before_environment(self):
        with patch.dict(os.environ, {}, clear=True), \
             patch('sys.argv', ['diag', '--packet', d.PACKET]), \
             patch.object(d.ci, 'environment') as env:
            with self.assertRaisesRegex(RuntimeError, 'only on hosted'):
                d.main()
            env.assert_not_called()

    def test_no_artifact_admission(self):
        source = Path(d.__file__).read_text()
        self.assertNotIn("'-o'", source)
        self.assertIn("dir=os.environ['RUNNER_TEMP']", source)
        self.assertIn("'baseline_or_experiment_accepted':False", source)
        self.assertIn('original.bounded(', source)
        self.assertEqual(d.original.MAX_BYTES, 2*1024*1024)
        self.assertEqual(d.original.SECONDS, 90)

if __name__ == '__main__':
    unittest.main()
