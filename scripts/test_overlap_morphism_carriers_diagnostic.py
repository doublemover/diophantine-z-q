#!/usr/bin/env python3
import hashlib
import unittest
from pathlib import Path
import diagnose_overlap_morphism_carriers as d
BASE=Path(__file__).resolve().parents[1]/'quartics/quartic-318-326/proof/experiments'
class OverlapCarrierTests(unittest.TestCase):
 def setUp(self):
  self.source=(BASE/d.PACKET/'OverlapMorphismCoaction318.lean').read_text()
  self.consumer=(BASE/d.PACKET/'GeometricAffineDescentData318.lean').read_text()
  self.v=d.variants(self.source,self.consumer)
 def test_helper_independent(self):
  self.assertIn('private lemma conjugate_square',self.v['generic_conjugation_only'])
  self.assertNotIn('lemma module_coaction',self.v['generic_conjugation_only'])
  self.assertNotIn('lemma sheaf_square',self.v['generic_conjugation_only'])
 def test_actual_producers_separate(self):
  self.assertIn('lemma module_coaction',self.v['actual_module_coaction'])
  self.assertNotIn('private lemma conjugate_square',self.v['actual_module_coaction'])
  self.assertIn('lemma sheaf_square',self.v['actual_sheaf_specialization'])
  self.assertNotIn('lemma geometric_coaction',self.v['actual_sheaf_specialization'])
 def test_actual_full_and_downstream(self):
  self.assertEqual(self.v['actual_full_geometric_consumer'],self.source)
  self.assertIn(self.consumer.split('public import OverlapMorphismCoaction318\n',1)[1],self.v['actual_next_descent_consumer'])
 def test_only_one_source_changed(self):
  old=BASE/'contact-relative-site-descent-r48';new=BASE/d.PACKET
  changes=[p.name for p in old.glob('*.lean') if p.read_bytes()!=(new/p.name).read_bytes()]
  self.assertEqual(changes,['OverlapMorphismCoaction318.lean'])
 def test_passing_sources_exact(self):
  for n,pin in [('OriginalGeometricDiagonal318',d.DIAGONAL_SHA),('AffineSplitDiagonalTranspose318',d.TRANSPOSE_SHA)]:
   self.assertEqual(hashlib.sha256((BASE/d.PACKET/(n+'.lean')).read_bytes()).hexdigest(),pin)
 def test_guarded_source(self):
  with self.assertRaises(AssertionError):d.variants(self.source+'\n',self.consumer)
 def test_no_admission_or_budget(self):
  for v in self.v.values():self.assertNotIn('sorry',v);self.assertNotIn('axiom ',v)
  self.assertEqual(len(self.v),5)
if __name__=='__main__':unittest.main()
