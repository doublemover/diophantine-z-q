#!/usr/bin/env python3
"""Pure source/harness tests only. Never invokes Lean locally."""
import hashlib
from pathlib import Path
import unittest
import diagnose_diagonal_components as d
class ComponentTests(unittest.TestCase):
    def setUp(self):
        self.root=Path('quartics/quartic-318-326/proof/experiments')
        self.source=(self.root/d.PACKET/'OriginalGeometricDiagonal318.lean').read_text()
    def test_binding(self):
        self.assertEqual(hashlib.sha256(self.source.encode()).hexdigest(),d.SOURCE_SHA)
    def test_no_sorry_no_final(self):
        v=d.variants(self.source)
        self.assertEqual(set(v),{'named_projection_components','named_split_prefix','componentwise_left_formula'})
        for text in v.values():
            self.assertNotIn('sorry',text)
            self.assertNotIn('lemma diagonal_to_split',text)
            self.assertTrue(text.endswith('end OriginalGeometricDiagonal318\n'))
        self.assertNotIn('lemma split_left_formula',v['named_projection_components'])
        self.assertIn('lemma split_sections ',v['named_split_prefix'])
    def test_componentwise_isolated(self):
        v=d.variants(self.source)
        text=v['componentwise_left_formula']
        self.assertNotIn('lemma split_mapIso_projection',text)
        self.assertNotIn('lemma split_sheaf_projection',text)
        self.assertNotIn('lemma split_sections ',text)
        self.assertIn('apply ModuleCat.hom_ext\n  ext x\n  rfl',text)
        self.assertIn('DIAGONAL positive control before split_left_formula',text)
        self.assertIn('DIAGONAL after split_left_formula',text)
        self.assertNotIn('apply ModuleCat.hom_ext',self.source)
    def test_scopes_and_original(self):
        v=d.variants(self.source)
        for name in d.NAMES[:-3]:
            self.assertIn('DIAGONAL positive control before '+name,v['named_projection_components'])
            self.assertIn('DIAGONAL after '+name,v['named_projection_components'])
        for n in ('OriginalGeometricEdge318','OriginalGeometricTriple318'):
            self.assertEqual((self.root/d.PACKET/(n+'.lean')).read_bytes(),
                (self.root/'contact-relative-site-descent-r29'/(n+'.lean')).read_bytes())
        old=(self.root/'contact-relative-site-descent-r34'/'OriginalGeometricDiagonal318.lean').read_text()
        self.assertEqual(self.source[self.source.index('lemma diagonal_to_split'):],old[old.index('lemma diagonal_to_split'):])
if __name__=='__main__':unittest.main()
