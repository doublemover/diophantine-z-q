#!/usr/bin/env python3
"""Pure source tests, never runs Lean."""
import hashlib
from pathlib import Path
import unittest
import diagnose_diagonal_split as d
class SplitTests(unittest.TestCase):
    def setUp(self):
        self.root=Path('quartics/quartic-318-326/proof/experiments')
        self.source=(self.root/d.PACKET/'OriginalGeometricDiagonal318.lean').read_text()
    def test_hash(self):
        self.assertEqual(hashlib.sha256(self.source.encode()).hexdigest(),d.SOURCE_SHA)
    def test_acceptance_scope(self):
        v=d.variants(self.source)
        self.assertEqual(set(v),{'opaque_split_prefix','opaque_split_full'})
        for name,text in v.items():
            self.assertNotIn('sorry',text)
            for n in d.NAMES[:4]:
                self.assertIn('diagnostic_positive_'+n+' : True',text)
                self.assertIn('DIAGONAL after '+n,text)
            self.assertEqual('lemma diagonal_to_split' in text,name.endswith('full'))
            self.assertTrue(text.endswith('end OriginalGeometricDiagonal318\n'))
    def test_doccomment_not_stolen(self):
        text=d.variants(self.source)['opaque_split_prefix']
        comment=text.index('/-- Opaque categorical')
        declaration=text.index('private lemma split_named')
        self.assertNotIn('run_cmd',text[comment:declaration])
        self.assertNotIn('set_option',text[comment:declaration])
        self.assertLess(text.index('diagnostic_positive_split_named'),comment)
    def test_accepted_predecessors_and_final_proof(self):
        for n in ('OriginalGeometricEdge318','OriginalGeometricTriple318'):
            self.assertEqual((self.root/d.PACKET/(n+'.lean')).read_bytes(),
                (self.root/'contact-relative-site-descent-r29'/(n+'.lean')).read_bytes())
        old=(self.root/'contact-relative-site-descent-r30'/'OriginalGeometricDiagonal318.lean').read_text()
        self.assertEqual(self.source[self.source.index('lemma diagonal_to_split'):],
            old[old.index('lemma diagonal_to_split'):])
if __name__=='__main__':unittest.main()
