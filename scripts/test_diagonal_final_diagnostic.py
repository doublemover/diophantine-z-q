import hashlib
from pathlib import Path
import unittest
import diagnose_diagonal_final as d
class FinalTests(unittest.TestCase):
 def setUp(self):
  self.root=Path('quartics/quartic-318-326/proof/experiments')
  self.source=(self.root/d.PACKET/'OriginalGeometricDiagonal318.lean').read_text()
 def test_binding(self):
  self.assertEqual(hashlib.sha256(self.source.encode()).hexdigest(),d.SOURCE_SHA)
 def test_final_targets(self):
  v=d.variants(self.source)
  self.assertEqual(set(v),{'clean_split_control','original_final','explicit_final'})
  for k,s in v.items():
   self.assertNotIn('sorry',s)
   self.assertIn('"DIAGONAL after split_sections"',s)
   if k!='clean_split_control':
    self.assertIn('lemma diagonal_to_split ',s)
    self.assertIn('"DIAGONAL after diagonal_to_split"',s)
    self.assertIn('diagnostic_positive_final :',s)
  self.assertNotIn('lemma diagonal_to_split ',v['clean_split_control'])
 def test_accepted_prefix_exact(self):
  old=(self.root/'contact-relative-site-descent-r41'/'OriginalGeometricDiagonal318.lean').read_text()
  self.assertEqual(self.source.split('lemma diagonal_to_split ')[0],old.split('lemma diagonal_to_split ')[0])
  for n in ('OriginalGeometricEdge318','OriginalGeometricTriple318'):
   self.assertEqual((self.root/d.PACKET/(n+'.lean')).read_bytes(),(self.root/'contact-relative-site-descent-r29'/(n+'.lean')).read_bytes())
 def test_hosted_safety(self):
  s=Path('scripts/diagnose_diagonal_final.py').read_text()
  self.assertIn("os.environ.get('GITHUB_ACTIONS')!='true'",s)
  self.assertIn('previous.bounded_memory',s)
  self.assertIn("'writes_olean':False",s)
  self.assertIn("PACKET = 'contact-relative-site-descent-r41'",Path('scripts/diagnose_diagonal_counit.py').read_text())
if __name__=='__main__':unittest.main()
