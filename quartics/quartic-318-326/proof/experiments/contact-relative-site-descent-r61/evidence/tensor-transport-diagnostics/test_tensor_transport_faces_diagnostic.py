#!/usr/bin/env python3
import hashlib,unittest
from pathlib import Path
import diagnose_tensor_transport_faces as d
BASE=d.ci.ROOT/'quartics/quartic-318-326/proof/experiments'
class Tests(unittest.TestCase):
 def setUp(self):
  self.source=(BASE/d.PACKET/'ActualAffineTensorTransport318.lean').read_text();self.consumer=(BASE/d.PACKET/'ActualAffineTensorLaws318.lean').read_text();self.v=d.variants(self.source,self.consumer)
 def test_generic_independent(self):
  self.assertIn('lemma affine_transport',self.v['generic_affine_transport_only']);self.assertNotIn('lemma native_face',self.v['generic_affine_transport_only']);self.assertNotIn('def overlap',self.v['generic_affine_transport_only'])
 def test_native_independent(self):
  self.assertIn('lemma native_face',self.v['actual_native_square_only']);self.assertIn('SheafPathTransport318.square',self.v['actual_native_square_only']);self.assertNotIn('lemma affine_transport',self.v['actual_native_square_only']);self.assertNotIn('lemma affine_face',self.v['actual_native_square_only'])
 def test_actual_specialization(self):
  self.assertIn('lemma affine_face',self.v['actual_affine_specialization_only']);self.assertIn('(overlap R S L τ)',self.v['actual_affine_specialization_only']);self.assertNotIn('lemma native_face',self.v['actual_affine_specialization_only'])
 def test_exact_final_and_downstream(self):
  self.assertEqual(self.source,self.v['actual_full_tensor_transport']);self.assertIn(self.consumer.split('public import ActualAffineTensorTransport318\n',1)[1],self.v['actual_downstream_tensor_laws'])
 def test_statement_and_other_sources(self):
  old=BASE/'contact-relative-site-descent-r56';new=BASE/d.PACKET
  self.assertEqual([p.name for p in old.glob('*.lean') if p.read_bytes()!=(new/p.name).read_bytes()],['ActualAffineTensorTransport318.lean'])
  orig=(old/'ActualAffineTensorTransport318.lean').read_text();self.assertEqual(orig[orig.index('lemma face ('):orig.index(' := by',orig.index('lemma face ('))],self.source[self.source.index('lemma face ('):self.source.index(' := by',self.source.index('lemma face ('))])
 def test_exact_producers_and_guard(self):
  for n,pin in d.PRODUCER_PINS.items():self.assertEqual(hashlib.sha256((BASE/d.PACKET/(n+'.lean')).read_bytes()).hexdigest(),pin)
  with self.assertRaises(AssertionError):d.variants(self.source+'\n',self.consumer)
 def test_no_admission_budget_or_acceptance_bypass(self):
  self.assertEqual(len(self.v),5)
  for v in self.v.values():self.assertNotIn('sorry',v);self.assertNotIn('axiom ',v)
  self.assertIn('baseline_or_experiment_accepted=False',Path(d.__file__).read_text())
if __name__=='__main__':unittest.main()
