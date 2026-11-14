#!/usr/bin/env python3
"""Python-only structural runner checks; no Lean or subprocess is executed."""
import hashlib,json,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import diagnose_common_expression_boundary as d
P=d.ci.ROOT/'quartics/quartic-318-326/proof/experiments'/d.previous.PACKET
S=(P/(d.previous.MODULE+'.lean')).read_text()
class Tests(unittest.TestCase):
    def test_two_exact_observers(self):
        cases=d.variants(S);self.assertEqual(list(cases),['exact_prefix','structural_witness'])
        self.assertEqual(cases['exact_prefix'],d.previous.variants(S)['exact_prefix'])
        self.assertIn(d.STRUCTURAL_BODY,cases['structural_witness'])
        self.assertEqual(hashlib.sha256(d.STRUCTURAL_BODY.encode()).hexdigest(),'07ded6f92099298335558139ab345ee9dc572fc357d2f857bf21a91ed4486d78')
        for text in cases.values():
            self.assertNotIn('sorry',text);self.assertNotIn('axiom ',text);self.assertNotIn('set_option maxRecDepth',text)
            self.assertEqual([x for x in S.splitlines() if 'import ' in x],[x for x in text.splitlines() if 'import ' in x])
        self.assertIn('e.flush',cases['exact_prefix']);self.assertIn('err.flush',cases['structural_witness'])
    def test_native_observer_scope(self):
        body=d.STRUCTURAL_BODY
        for term in ['Lean.Elab.Tactic.withMainContext','Lean.Meta.inferType','Lean.Meta.getFVarFromUserName','Lean.Expr.equal','for _ in [:1024]','differences >= 8','METADATA_PAYLOAD_NOT_COMPARED','exact True.intro']:self.assertIn(term,body)
        for term in ['Lean.Meta.isDefEq','Lean.Meta.whnf','.assign ', 'addDecl ', 'setEnv ', 'set_option pp.']:self.assertNotIn(term,body)
        self.assertIn('Structural difference does not prove definitional inequality',body)
    def test_pinned_dependency_guards(self):
        d.check_dependencies()
        for name in d.DEPENDENCY_PINS:
            if name.endswith('.yml'):continue
            with self.subTest(name=name),patch.dict(d.DEPENDENCY_PINS,{name:'changed'}):
                with self.assertRaisesRegex(ValueError,'Pinned diagnostic dependency changed'):d.check_dependencies()
    def test_original_source_guard(self):
        with self.assertRaisesRegex(ValueError,'Frozen source changed'):d.variants(S+'\n')
    def test_inherited_hosted_and_flags_guards(self):
        with patch.dict(d.os.environ,{},clear=True):
            with self.assertRaisesRegex(ValueError,'Hosted Actions only'):d.validate(P,Path('/missing'))
        with patch.object(d.ci,'FLAGS',[]):
            with self.assertRaisesRegex(ValueError,'Strict compiler flags changed'):d.validate(P,Path('/missing'),False)
    def test_complete_guarded_fixture(self):
        intake=json.loads((P/'intake.json').read_text());order=intake['order'][:intake['order'].index(d.previous.MODULE)+1]
        r={'packet':d.previous.PACKET,'packet_sha256':d.previous.INTAKE_SHA,'commands':[{'module':n,'exit_code':int(n==d.previous.MODULE)} for n in order]}
        with tempfile.TemporaryDirectory() as temp:
            out=Path(temp);(out/'lib').mkdir();(out/'lib/LocalizedTensorRestriction318.olean').write_text('presence-only fixture, never loaded');(out/'RESULT.json').write_text(json.dumps(r))
            self.assertEqual(len(d.validate(P,out,False)[0]),2)
            (out/'lib'/(d.previous.MODULE+'.olean')).write_text('negative presence fixture')
            with self.assertRaisesRegex(ValueError,'Unexpected compiled artifacts'):d.validate(P,out,False)
    def test_no_compiled_output_or_acceptance(self):
        source=Path(d.__file__).read_text();self.assertNotIn("'-o'",source)
        self.assertIn('previous.require_no_compiled_artifacts(root)',source)
        self.assertIn("previous.require_no_compiled_artifacts(output/'lib',previous.MODULE)",source)
        for field in ['full_packet_accepted','baseline_or_experiment_accepted','writes_olean','production_source_changed']:self.assertIn("'"+field+"':False",source)
        self.assertIn('not a bound on work within inferType or Expr.equal',source)
if __name__=='__main__':unittest.main()
