#!/usr/bin/env python3
"""Pure source tests, never invokes Lean."""
import hashlib
from pathlib import Path
import unittest
import diagnose_named_edge as d
class NamedEdgeTests(unittest.TestCase):
    def setUp(self):
        p=Path('quartics/quartic-318-326/proof/experiments')/d.PACKET/'OriginalGeometricEdge318.lean'
        self.raw=p.read_bytes(); self.source=self.raw.decode()
    def test_source_binding(self):
        self.assertEqual(hashlib.sha256(self.raw).hexdigest(), d.SOURCE_SHA)
        self.assertEqual(set(d.variants(self.source)), {'named_endpoint_only','named_through_edge'})
    def test_exact_complete_edge(self):
        variant=d.variants(self.source)['named_through_edge']
        start=self.source.index('private lemma edge_formula')
        stop=self.source.index('\nrun_cmd ', self.source.index('lemma edge_to_module'))
        self.assertIn(self.source[start:stop], variant)
        self.assertNotIn('lemma edge_to_module', d.variants(self.source)['named_endpoint_only'])
    def test_no_sorry_and_scope(self):
        for text in d.variants(self.source).values():
            self.assertNotIn('sorry',text)
            self.assertIn('set_option profiler.threshold 0',text)
            self.assertTrue(text.endswith('end OriginalGeometricEdge318\n'))
if __name__=='__main__': unittest.main()
