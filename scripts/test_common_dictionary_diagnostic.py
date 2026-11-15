#!/usr/bin/env python3
"""Python-only checks for the nonadmitted Common dictionary probes. Never invokes Lean."""
import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import diagnose_common_dictionary_conversion as d
P = d.ci.ROOT/'quartics/quartic-318-326/proof/experiments'/d.witness.PACKET
S = (P/(d.witness.MODULE+'.lean')).read_text()
class Tests(unittest.TestCase):
    def test_two_exact_hash_bound_probes(self):
        cases=d.variants(S)
        self.assertEqual(list(cases),['restricted_dictionary_dsimp','instance_transparency_witness'])
        self.assertEqual({n:hashlib.sha256(s.encode()).hexdigest() for n,s in cases.items()}, {
            'restricted_dictionary_dsimp':'1e012ab6936e495ea63d808791491025d1a8f7f5ba532aebcb67be368d7c6650',
            'instance_transparency_witness':'8bfe67016f2a5a795417ad54f2ad44b344007df2d28742a061f2aa8e5d69e55b'})
    def test_import_options_and_full_lift_endpoint(self):
        for name,t in d.variants(S).items():
            self.assertEqual([x for x in S.splitlines() if 'import ' in x],[x for x in t.splitlines()if 'import ' in x])
            for flag in ['set_option maxHeartbeats 1200000','set_option synthInstance.maxSize 4096','set_option backward.isDefEq.respectTransparency false','set_option backward.isDefEq.respectTransparency.types false']:
                self.assertIn(flag,t)
            self.assertIn('have completed := lift (by',t)
            self.assertIn('exact True.intro',t)
            self.assertNotIn('def commonRestriction',t)
            for forbidden in ['sorry','axiom ','set_option maxRecDepth','debug.skipKernelTC true']:
                self.assertNotIn(forbidden,t)
    def test_narrow_dictionary_hypothesis(self):
        a=d.NORMALIZERS['restricted_dictionary_dsimp']
        for n in ['oldOverlapCommRing','CommRing.toCommSemiring','CommSemiring.toSemiring','Algebra.TensorProduct.instCommRing','Algebra.TensorProduct.instRing','at hX ⊢']:
            self.assertIn(n,a)
        self.assertNotIn('simp_all',a)
        self.assertNotIn('Algebra.TensorProduct.instSemiring',a)
        self.assertIn('with_reducible_and_instances',d.NORMALIZERS['instance_transparency_witness'])
    def test_frozen_source_and_dependency_guards(self):
        d.check_dependencies()
        with self.assertRaisesRegex(ValueError,'Frozen source changed'):d.variants(S+'\n')
        with patch.object(d,'DEPENDENCY_SHA','wrong'):
            with self.assertRaisesRegex(ValueError,'Pinned structural diagnostic changed'):d.check_dependencies()
    def test_hosted_and_strict_guards(self):
        with patch.dict(os.environ,{},clear=True):
            with self.assertRaisesRegex(ValueError,'Hosted Actions only'):d.validate(P,Path('/missing'))
        with patch.object(d.ci,'FLAGS',[]):
            with self.assertRaisesRegex(ValueError,'Strict compiler flags changed'):d.validate(P,Path('/missing'),False)
    def test_guarded_fixture_and_changed_frontier(self):
        intake=json.loads((P/'intake.json').read_text())
        order=intake['order'][:intake['order'].index(d.witness.MODULE)+1]
        r={'packet':d.witness.PACKET,'packet_sha256':d.witness.INTAKE_SHA,'commands':[{'module':n,'exit_code':int(n==d.witness.MODULE)} for n in order]}
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp);(out/'lib').mkdir()
            (out/'lib/LocalizedTensorRestriction318.olean').write_text('presence-only fixture, never loaded')
            rp=out/'RESULT.json';rp.write_text(json.dumps(r))
            self.assertEqual(len(d.validate(P,out,False)[0]),2)
            r['commands'][-1]['exit_code']=0;rp.write_text(json.dumps(r))
            with self.assertRaisesRegex(ValueError,'Ordinary outcomes changed'):d.validate(P,out,False)
    def test_compiled_artifact_negative_guard(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp);(p/'unexpected.olean').write_text('not loaded')
            with self.assertRaisesRegex(ValueError,'Unexpected compiled artifacts'):d.witness.require_no_compiled_artifacts(p)
    def test_limits_runner_and_nonacceptance(self):
        self.assertEqual(d.witness.SECONDS,90);self.assertEqual(d.witness.MAX_BYTES,2*1024*1024)
        src=Path(d.__file__).read_text()
        self.assertIn('witness.runner.bounded_memory',src)
        self.assertNotIn("'-o'",src)
        self.assertIn('logs.mkdir(exist_ok=False)',src)
        self.assertIn("'scratch-common-expression-diagnostics'",src)
        for key in ['full_packet_accepted','baseline_or_experiment_accepted','writes_olean','production_source_changed']:
            self.assertIn("'"+key+"': False",src)
        self.assertIn('not full commonRestriction',src)
if __name__=='__main__':unittest.main()
