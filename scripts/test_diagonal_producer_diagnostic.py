#!/usr/bin/env python3
"""Pure text/source tests only. No local Lean invocation."""
import hashlib
from pathlib import Path
import unittest
import diagnose_diagonal_producer as d
class ProducerTests(unittest.TestCase):
    def setUp(self):
        self.root=Path('quartics/quartic-318-326/proof/experiments')
        self.source=(self.root/d.PACKET/'OriginalGeometricDiagonal318.lean').read_text()
    def test_binding(self):
        self.assertEqual(hashlib.sha256(self.source.encode()).hexdigest(),d.SOURCE_SHA)
    def test_all_actual_targets_retained(self):
        v=d.variants(self.source)
        expected={'generic_composition':'sections_composition_generic',
          'concrete_composition':'split_composition_explicit',
          'identity_isolated':'split_identity_explicit','clean_split':'split_sections'}
        self.assertEqual(set(v),set(expected))
        for key,name in expected.items():
            self.assertIn('lemma '+name+' ',v[key])
            self.assertIn('"DIAGONAL after '+name+'"',v[key])
            self.assertNotIn('sorry',v[key]);self.assertNotIn('lemma diagonal_to_split',v[key])
            self.assertTrue(v[key].endswith('end OriginalGeometricDiagonal318\n'))
    def test_marker_collision_and_independent_identity(self):
        v=d.variants(self.source)
        # The earlier projection marker exists but must not truncate identity.
        self.assertIn('diagnostic_positive_split_sections_projection :',v['identity_isolated'])
        self.assertIn('lemma split_identity_explicit ',v['identity_isolated'])
        self.assertNotIn('lemma sections_composition_generic ',v['identity_isolated'])
        self.assertNotIn('lemma split_composition_explicit ',v['identity_isolated'])
        self.assertNotIn('lemma split_sections ',v['identity_isolated'])
        self.assertNotIn('lemma split_identity_explicit ',v['concrete_composition'])
    def test_preserved_accepted_sources_final_and_old_harness(self):
        for n in ('OriginalGeometricEdge318','OriginalGeometricTriple318'):
            self.assertEqual((self.root/d.PACKET/(n+'.lean')).read_bytes(),
                (self.root/'contact-relative-site-descent-r29'/(n+'.lean')).read_bytes())
        old=(self.root/'contact-relative-site-descent-r39'/'OriginalGeometricDiagonal318.lean').read_text()
        self.assertEqual(self.source[self.source.index('lemma diagonal_to_split'):],old[old.index('lemma diagonal_to_split'):])
        self.assertIn("PACKET = 'contact-relative-site-descent-r39'",Path('scripts/diagnose_diagonal_split_specialization.py').read_text())
if __name__=='__main__':unittest.main()
