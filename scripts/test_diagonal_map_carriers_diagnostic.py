#!/usr/bin/env python3
"""Pure source/harness tests. Never invoke Lean locally."""
import hashlib
from pathlib import Path
import unittest
import diagnose_diagonal_map_carriers as d
class MapCarrierTests(unittest.TestCase):
    def setUp(self):
        self.root=Path('quartics/quartic-318-326/proof/experiments')
        self.source=(self.root/d.PACKET/'OriginalGeometricDiagonal318.lean').read_text()
    def test_binding(self):
        self.assertEqual(hashlib.sha256(self.source.encode()).hexdigest(),d.SOURCE_SHA)
    def test_no_sorry_no_final(self):
        v=d.variants(self.source)
        self.assertEqual(set(v),{'abstract_functor_map','direct_explicit_map','original_mapped_signature','explicit_map_split_prefix'})
        for text in v.values():
            self.assertNotIn('sorry',text)
            self.assertNotIn('lemma diagonal_to_split',text)
            self.assertTrue(text.endswith('end OriginalGeometricDiagonal318\n'))
        self.assertNotIn('lemma split_mapped_explicit',v['abstract_functor_map'])
        self.assertIn('lemma split_sections ',v['explicit_map_split_prefix'])
    def test_direct_isolated(self):
        v=d.variants(self.source);text=v['direct_explicit_map']
        self.assertNotIn('lemma split_mapped_generic',text)
        self.assertNotIn('lemma split_mapped_projection',text)
        self.assertIn('congrArg (fun h :',text)
        self.assertIn('(moduleSpecΓFunctor (R := S)).map (X :=',text)
        self.assertIn('DIAGONAL positive control before split_mapped_explicit',text)
        self.assertIn('DIAGONAL after split_mapped_explicit',text)
    def test_accepted_sources_and_final(self):
        for n in ('OriginalGeometricEdge318','OriginalGeometricTriple318'):
            self.assertEqual((self.root/d.PACKET/(n+'.lean')).read_bytes(),
                (self.root/'contact-relative-site-descent-r29'/(n+'.lean')).read_bytes())
        old=(self.root/'contact-relative-site-descent-r35'/'OriginalGeometricDiagonal318.lean').read_text()
        self.assertEqual(self.source[self.source.index('lemma diagonal_to_split'):],old[old.index('lemma diagonal_to_split'):])
if __name__=='__main__':unittest.main()
