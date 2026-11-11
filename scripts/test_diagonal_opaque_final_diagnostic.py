import hashlib
from pathlib import Path
import unittest
import diagnose_diagonal_opaque_final as d
class OpaqueFinalTests(unittest.TestCase):
    def setUp(self):
        self.root=Path('quartics/quartic-318-326/proof/experiments')
        self.candidate=self.root/d.PACKET
        self.original=self.root/'contact-relative-site-descent-r43'
        self.source=(self.candidate/'OriginalGeometricDiagonal318.lean').read_text()
        self.old=(self.original/'OriginalGeometricDiagonal318.lean').read_text()
        self.consumer=(self.candidate/'AffineSplitDiagonalTranspose318.lean').read_text()
    def test_exact_one_production_change(self):
        changed=[p.name for p in self.candidate.glob('*.lean') if p.read_bytes()!=(self.original/p.name).read_bytes()]
        self.assertEqual(changed,['OriginalGeometricDiagonal318.lean'])
    def test_helpers_and_final_independent(self):
        v=d.variants(self.source,self.old,self.consumer)
        self.assertEqual(set(v),{'clean_split_control','opaque_helper_only','original_final_control','opaque_final','opaque_final_actual_consumer'})
        self.assertNotIn('lemma diagonal_to_split ',v['opaque_helper_only'])
        self.assertNotIn('lemma diagonal_compose ',v['clean_split_control'])
        self.assertEqual(v['opaque_final'],self.source)
        self.assertEqual(v['original_final_control'],self.old)
    def test_actual_downstream_bytes(self):
        v=d.variants(self.source,self.old,self.consumer)['opaque_final_actual_consumer']
        self.assertIn(self.consumer.split('public import OriginalGeometricDiagonal318\n',1)[1],v)
        self.assertIn('lemma diagonal_to_module ',v)
        self.assertIn('"DIAGONAL actual downstream consumer completed"',v)
    def test_final_no_concrete_rewrite(self):
        final=self.source.split('lemma diagonal_to_split ',1)[1]
        self.assertIn('exact diagonal_compose',final)
        for tactic in ('\n  rw [','\n  simp ','\n  change '):self.assertNotIn(tactic,final)
        self.assertIn('set_option profiler true in\nset_option profiler.threshold 0 in\nlemma diagonal_to_split ',self.source)
    def test_hosted_safety(self):
        s=Path('scripts/diagnose_diagonal_opaque_final.py').read_text()
        self.assertIn("os.environ.get('GITHUB_ACTIONS')!='true'",s)
        self.assertIn('previous.bounded_memory',s)
        self.assertIn("'writes_olean':False",s)
        self.assertNotIn("'-o'",s)
if __name__=='__main__':unittest.main()
