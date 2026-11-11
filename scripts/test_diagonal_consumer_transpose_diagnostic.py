#!/usr/bin/env python3
import unittest
from pathlib import Path
import diagnose_diagonal_consumer_transpose as d
BASE=Path(__file__).resolve().parents[1]/'quartics/quartic-318-326/proof/experiments'
class ConsumerTransposeTests(unittest.TestCase):
 def setUp(self):
  self.source=(BASE/d.PACKET/'OriginalGeometricDiagonal318.lean').read_text()
  self.consumer=(BASE/d.PACKET/'AffineSplitDiagonalTranspose318.lean').read_text()
  self.old=(BASE/'contact-relative-site-descent-r46'/'OriginalGeometricDiagonal318.lean').read_text()
  self.v=d.variants(self.source,self.consumer,self.old)
 def test_exact_diagonal_retained(self):
  self.assertEqual(self.v['unchanged_full_final'],self.old)
 def test_actual_consumer_both_routes(self):
  self.assertTrue(self.v['actual_consumer_imported'].startswith(self.consumer))
  self.assertIn(self.consumer.split('public import OriginalGeometricDiagonal318\n',1)[1],self.v['full_final_actual_consumer'])
 def test_only_consumer_delta(self):
  old=(BASE/'contact-relative-site-descent-r46'/'AffineSplitDiagonalTranspose318.lean').read_text()
  self.assertEqual(self.consumer,old.replace(
   '  simpa only [Adjunction.homEquiv_naturality_left, first_transpose, second_transpose] using h',
   '  simpa only [OriginalGeometricDiagonal318.diagonal, OriginalLineOverlapCoaction318.sections,\n    Adjunction.homEquiv_naturality_left, first_transpose, second_transpose] using h'))
 def test_guarded_source(self):
  with self.assertRaises(AssertionError):d.variants(self.source+'\n',self.consumer,self.old)
 def test_no_admission_or_budget(self):
  for v in self.v.values():self.assertNotIn('sorry',v);self.assertNotIn('axiom ',v)
  self.assertEqual(len(self.v),3)
if __name__=='__main__':unittest.main()
