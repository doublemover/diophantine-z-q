#!/usr/bin/env python3
"""Pure source/harness tests. Never invoke Lean locally."""
import hashlib
from pathlib import Path
import unittest
import diagnose_diagonal_split_specialization as d
class SplitSpecializationTests(unittest.TestCase):
    def setUp(self):
        self.root=Path('quartics/quartic-318-326/proof/experiments')
        self.source=(self.root/d.PACKET/'OriginalGeometricDiagonal318.lean').read_text()
    def test_binding(self):
        self.assertEqual(hashlib.sha256(self.source.encode()).hexdigest(),d.SOURCE_SHA)
    def test_no_sorry_no_final(self):
        v=d.variants(self.source)
        self.assertEqual(set(v),{'typed_composition','typed_identity','typed_split_specialization'})
        for text in v.values():
            self.assertNotIn('sorry',text)
            self.assertNotIn('lemma diagonal_to_split',text)
            self.assertTrue(text.endswith('end OriginalGeometricDiagonal318\n'))
        self.assertNotIn('lemma split_identity_explicit',v['typed_composition'])
        self.assertNotIn('lemma split_sections ',v['typed_identity'])
        self.assertIn('lemma split_sections ',v['typed_split_specialization'])
    def test_explicit_consumers(self):
        text=d.variants(self.source)['typed_split_specialization']
        self.assertNotIn('moduleSpecΓFunctor.map',text)
        self.assertIn('(moduleSpecΓFunctor (R := S)).map (X :=',text)
        self.assertIn('(A := ((Scheme.Modules.pullback',text)
        self.assertIn('(Z := extendedSections (𝟙 S) L)',text)
        self.assertIn('DIAGONAL positive control before split_sections',text)
        self.assertIn('DIAGONAL after split_sections',text)
    def test_accepted_sources_and_final(self):
        for n in ('OriginalGeometricEdge318','OriginalGeometricTriple318'):
            self.assertEqual((self.root/d.PACKET/(n+'.lean')).read_bytes(),
                (self.root/'contact-relative-site-descent-r29'/(n+'.lean')).read_bytes())
        old=(self.root/'contact-relative-site-descent-r35'/'OriginalGeometricDiagonal318.lean').read_text()
        self.assertEqual(self.source[self.source.index('lemma diagonal_to_split'):],old[old.index('lemma diagonal_to_split'):])
if __name__=='__main__':unittest.main()
