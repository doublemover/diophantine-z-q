#!/usr/bin/env python3
"""Pure source comparisons only; no local Lean."""
import hashlib
from pathlib import Path
import unittest
import diagnose_diagonal_formula as d
class FormulaTests(unittest.TestCase):
    def setUp(self):
        self.root=Path('quartics/quartic-318-326/proof/experiments')
        self.source=(self.root/d.PACKET/'OriginalGeometricDiagonal318.lean').read_text()
    def test_binding(self):
        self.assertEqual(hashlib.sha256(self.source.encode()).hexdigest(),d.SOURCE_SHA)
    def test_scopes(self):
        v=d.variants(self.source)
        self.assertEqual(set(v),{'generic_formula_only','generic_split_prefix','generic_split_full','direct_rfl_formula_only'})
        for name,text in v.items():
            self.assertNotIn('sorry',text)
            self.assertIn('DIAGONAL positive control before split_left_formula',text)
            self.assertIn('DIAGONAL after split_left_formula',text)
            self.assertEqual('lemma diagonal_to_split' in text,name=='generic_split_full')
            self.assertEqual('lemma split_sections' in text,name in ('generic_split_prefix','generic_split_full'))
            self.assertTrue(text.endswith('end OriginalGeometricDiagonal318\n'))
    def test_rfl_diagnostic_only(self):
        v=d.variants(self.source)
        original=v['generic_formula_only'];alternate=v['direct_rfl_formula_only']
        start=original.index(' := by',original.index('private lemma split_left_formula'))
        stop=original.index('\nrun_cmd do',start)
        self.assertEqual(alternate,original[:start]+' := by\n  rfl\n'+original[stop:])
        self.assertIn('exact mapped_iso_formula',self.source)
    def test_doccomments_and_retained_proof(self):
        text=d.variants(self.source)['generic_split_prefix']
        for marker,name in [('/-- Opaque categorical','split_named'),('/-- Projection identity','mapped_iso_formula')]:
            segment=text[text.index(marker):text.index('private lemma '+name)]
            self.assertNotIn('run_cmd',segment);self.assertNotIn('set_option',segment)
        for n in ('OriginalGeometricEdge318','OriginalGeometricTriple318'):
            self.assertEqual((self.root/d.PACKET/(n+'.lean')).read_bytes(),
                (self.root/'contact-relative-site-descent-r29'/(n+'.lean')).read_bytes())
        old=(self.root/'contact-relative-site-descent-r30'/'OriginalGeometricDiagonal318.lean').read_text()
        self.assertEqual(self.source[self.source.index('lemma diagonal_to_split'):],old[old.index('lemma diagonal_to_split'):])
if __name__=='__main__':unittest.main()
