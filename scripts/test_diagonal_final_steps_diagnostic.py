import hashlib
from pathlib import Path
import unittest
import diagnose_diagonal_final_steps as d
class FinalStepsTests(unittest.TestCase):
    def setUp(self):
        self.root=Path('quartics/quartic-318-326/proof/experiments')
        self.source=(self.root/d.PACKET/'OriginalGeometricDiagonal318.lean').read_text()
    def test_binding_and_production_preservation(self):
        self.assertEqual(hashlib.sha256(self.source.encode()).hexdigest(),d.SOURCE_SHA)
        for source in (self.root/d.PACKET).glob('*.lean'):
            self.assertEqual(source.read_bytes(),(self.root/'contact-relative-site-descent-r42'/source.name).read_bytes())
    def test_all_targets(self):
        v=d.variants(self.source)
        self.assertEqual(set(v),{'clean_split_control','statement','overlap','pulled',
            'left_split','right_split','mapped_diagonal','abstract_cancellation','explicit_final_control'})
        for name,text in v.items():
            self.assertNotIn('sorry',text)
            self.assertIn('"DIAGONAL after split_sections"',text)
            if name not in ('clean_split_control','explicit_final_control'):
                self.assertIn('"DIAGONAL final step '+name+'"',text)
                self.assertIn('diagnostic_positive_final_step :',text)
            if name != 'explicit_final_control':
                self.assertNotIn('lemma diagonal_to_split ',text)
    def test_statement_has_no_assumed_final_proof(self):
        s=d.variants(self.source)['statement']
        self.assertIn('private def diagnostic_final_statement : Prop :=',s)
        self.assertNotIn('(hτ :',s[s.index('private def diagnostic_final_statement'):])
        self.assertIn('OriginalLineOverlapCoaction318.moduleHomEquiv R S L τ',s)
    def test_producer_probes_are_separate(self):
        v=d.variants(self.source)
        for name in ('overlap','pulled','left_split','right_split'):
            for other in ('overlap','pulled','left_split','right_split'):
                self.assertEqual('private def diagnostic_'+other+' :=' in v[name],name==other)
    def test_original_control_exact(self):
        token=d.SCOPE+'lemma diagonal_to_split '
        self.assertEqual(d.variants(self.source)['explicit_final_control'].split(token)[1],self.source.split(token)[1])
    def test_hosted_safety(self):
        s=Path('scripts/diagnose_diagonal_final_steps.py').read_text()
        self.assertIn("os.environ.get('GITHUB_ACTIONS') != 'true'",s)
        self.assertIn('previous.bounded_memory',s)
        self.assertIn("'writes_olean':False",s)
        self.assertNotIn("'-o'",s)
        self.assertNotIn('skipKernelTC=true',s)
if __name__=='__main__': unittest.main()
