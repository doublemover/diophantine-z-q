#!/usr/bin/env python3
"""Pure text/safety tests; never invokes Lean."""
import hashlib
from pathlib import Path
import unittest
import diagnose_edge_elaboration as d

class EdgeProbeTests(unittest.TestCase):
    def setUp(self):
        p = Path('quartics/quartic-318-326/proof/experiments')/d.PACKET/'OriginalGeometricEdge318.lean'
        self.raw = p.read_bytes()
        self.source = self.raw.decode()
    def test_source_binding_and_scopes(self):
        self.assertEqual(hashlib.sha256(self.raw).hexdigest(), d.SOURCE_SHA)
        for text, _ in d.variants(self.source).values():
            self.assertIn('set_option diagnostics true in', text)
            self.assertTrue(text.endswith('end OriginalGeometricEdge318\n'))
            self.assertIn('private lemma endpoint_square', text)
    def test_sorry_is_isolated_and_labeled(self):
        variants = d.variants(self.source)
        self.assertEqual(len(variants), 3)
        for name, (text, flag) in variants.items():
            self.assertEqual('sorry' in text, flag)
            self.assertEqual(flag, name == 'edge_statement_only')
    def test_exact_rhs_and_original(self):
        start = self.source.index('lemma edge_to_module')
        stop = self.source.index('\nrun_cmd ', start)
        edge = self.source[start:stop]
        term = edge.split(' :=\n', 1)[1]
        self.assertIn(edge, d.variants(self.source)['edge_original_diagnostics'][0])
        self.assertIn('private def inferred_edge :=\n' + term,
                      d.variants(self.source)['edge_inferred_rhs'][0])

if __name__ == '__main__':
    unittest.main()
