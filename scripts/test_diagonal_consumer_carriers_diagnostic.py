#!/usr/bin/env python3
import unittest
from pathlib import Path
import diagnose_diagonal_consumer_carriers as d
BASE=Path(__file__).resolve().parents[1]/'quartics/quartic-318-326/proof/experiments'
class ConsumerCarrierTests(unittest.TestCase):
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
 def test_exact_transpose_proof_bodies(self):
  old=(BASE/'contact-relative-site-descent-r47'/'AffineSplitDiagonalTranspose318.lean').read_text()
  for n in ['first_transpose','second_transpose']:
   def body(s):return s.split('lemma '+n,1)[1].split(':= by',1)[1].split('\n\n',1)[0]
   self.assertEqual(body(self.consumer),body(old))
 def test_explicit_carriers_and_direct_composition(self):
  self.assertIn('(AffineOverlapCoaction318.first R S N) N',self.consumer)
  self.assertIn('(AffineOverlapCoaction318.second R S N) N',self.consumer)
  self.assertIn("(h'.trans (first_transpose",self.consumer)
  self.assertNotIn('first_transpose, second_transpose] using h',self.consumer)
 def test_separate_actual_producers(self):
  self.assertIn('lemma first_transpose',self.v['typed_first_transpose'])
  self.assertNotIn('lemma second_transpose',self.v['typed_first_transpose'])
  self.assertIn('lemma second_transpose',self.v['typed_second_transpose'])
  self.assertNotIn('lemma first_transpose',self.v['typed_second_transpose'])
 def test_guarded_source(self):
  with self.assertRaises(AssertionError):d.variants(self.source+'\n',self.consumer,self.old)
 def test_no_admission_or_budget(self):
  for v in self.v.values():self.assertNotIn('sorry',v);self.assertNotIn('axiom ',v)
  self.assertEqual(len(self.v),5)
if __name__=='__main__':unittest.main()
