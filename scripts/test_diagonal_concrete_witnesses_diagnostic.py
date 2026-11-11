#!/usr/bin/env python3
import unittest
from pathlib import Path
import diagnose_diagonal_concrete_witnesses as d
BASE=Path(__file__).resolve().parents[1]/'quartics/quartic-318-326/proof/experiments'
class ConcreteWitnessTests(unittest.TestCase):
 def setUp(self):
  self.source=(BASE/d.PACKET/'OriginalGeometricDiagonal318.lean').read_text()
  self.previous=(BASE/'contact-relative-site-descent-r44'/'OriginalGeometricDiagonal318.lean').read_text()
  self.consumer=(BASE/d.PACKET/'AffineSplitDiagonalTranspose318.lean').read_text()
  self.v=d.variants(self.source,self.previous,self.consumer)
 def test_eight_variants(self): self.assertEqual(len(self.v),8)
 def test_individual_witnesses_have_exact_types(self):
  for w in d.WITNESSES:
   self.assertIn('private lemma '+w+' :\n',self.v[w])
   self.assertEqual(sum('private lemma '+x+' ' in self.v[w] for x in d.WITNESSES),1)
 def test_real_producers(self):
  self.assertIn('OriginalGeometricTriple318.overlap_map',self.v['concrete_overlap'])
  self.assertIn('AffineSectionConjugation318.pulled_morphism',self.v['concrete_pulled'])
  for side in ('left','right'):self.assertIn('split_sections ('+side+'Map',self.v['concrete_'+side+'_split'])
 def test_full_and_consumer(self):
  self.assertEqual(self.v['concrete_final'],self.source)
  self.assertIn(self.consumer.split('public import OriginalGeometricDiagonal318\n',1)[1],self.v['concrete_final_actual_consumer'])
 def test_no_admissions_or_output_flags(self):
  for v in self.v.values():self.assertNotIn('sorry',v);self.assertNotIn('axiom ',v)
 def test_hash_guard(self):
  with self.assertRaises(AssertionError):d.variants(self.source+'\n',self.previous,self.consumer)
if __name__=='__main__':unittest.main()
