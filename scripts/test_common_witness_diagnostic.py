#!/usr/bin/env python3
"""Static/mock tests only; never execute Lean or a diagnostic process."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import diagnose_common_witness_conversion as d
P=d.ci.ROOT/'quartics/quartic-318-326/proof/experiments'/d.PACKET
S=(P/(d.MODULE+'.lean')).read_text()
class Tests(unittest.TestCase):
    def test_exact_sources_and_limits(self):
        cases=d.variants(S);self.assertEqual(len(cases),6)
        original=[x for x in S.splitlines() if x.startswith('set_option ')]
        for text in cases.values():
            self.assertNotIn('sorry',text);self.assertNotIn('axiom ',text);self.assertNotIn('set_option maxRecDepth',text)
            self.assertEqual([x for x in text.splitlines() if x.startswith('set_option ') and not x.startswith(('set_option diagnostics','set_option profiler','set_option stderrAsMessages','set_option pp.'))],original)
            self.assertIn('set_option stderrAsMessages false',text);self.assertIn('let e ← IO.getStderr',text);self.assertIn('e.flush',text)
            self.assertNotIn('theorem common_finite',text)
        prefix=cases['exact_prefix'].split('\nset_option diagnostics true')[0];self.assertTrue(S.startswith(prefix))
        body=cases['exact_staged_definition'].split('e.flush\n',1)[1].rsplit('\nend ',1)[0].strip();self.assertIn(body,S)
    def test_witnesses_and_output_options(self):
        c=d.variants(S)
        self.assertIn('set_option pp.explicit true\nset_option pp.universes true',c['explicit_equations'])
        self.assertIn('#check finiteRestriction_X R c',c['explicit_equations'])
        self.assertIn('#check liftOfAlgHomUnit',c['explicit_equations'])
        self.assertIn('change finiteRestriction R c',c['literal_expected_witness'])
        self.assertIn('exact finiteRestriction_X R c',c['literal_expected_witness'])
        self.assertIn('simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hX',c['normalized_coercion_witness'])
    def test_source_mutation(self):
        with self.assertRaisesRegex(ValueError,'Frozen source'):d.variants(S+'\n')
    def test_hosted_guard(self):
        with patch.dict(d.os.environ,{},clear=True):
            with self.assertRaisesRegex(ValueError,'Hosted Actions only'):d.validate(P,Path('/missing'))
    def fixture(self):
        data=json.loads((P/'intake.json').read_text());order=data['order'][:data['order'].index(d.MODULE)+1]
        return {'packet':d.PACKET,'packet_sha256':d.INTAKE_SHA,'commands':[{'module':n,'exit_code':int(n==d.MODULE)} for n in order]}
    def test_result_guards(self):
        with tempfile.TemporaryDirectory() as t:
            o=Path(t);rp=o/'RESULT.json'
            with self.assertRaisesRegex(ValueError,'Mandatory full'):d.validate(P,o,False)
            rp.write_text('{}')
            with self.assertRaisesRegex(ValueError,'Wrong full'):d.validate(P,o,False)
            r=self.fixture();r['commands']=r['commands'][:-1];rp.write_text(json.dumps(r))
            with self.assertRaisesRegex(ValueError,'frontier changed'):d.validate(P,o,False)
            r=self.fixture();r['commands'][-1]['exit_code']=0;rp.write_text(json.dumps(r))
            with self.assertRaisesRegex(ValueError,'outcomes changed'):d.validate(P,o,False)
    def test_dependency_and_caps(self):
        with tempfile.TemporaryDirectory() as t:
            o=Path(t);(o/'RESULT.json').write_text(json.dumps(self.fixture()))
            with self.assertRaisesRegex(ValueError,'dependency missing'):d.validate(P,o,False)
            (o/'lib').mkdir();(o/'lib/LocalizedTensorRestriction318.olean').write_text('static test fixture, never loaded')
            self.assertEqual(len(d.validate(P,o,False)[0]),6)
            with patch.object(d.runner.original,'MAX_BYTES',1):
                with self.assertRaisesRegex(ValueError,'caps changed'):d.validate(P,o,False)
    def test_strict_flags(self):
        for flags in [[],["-j1","-M","6144"],["-j1","-M","6144","-Ddebug.skipKernelTC=true"],[*d.EXPECTED_FLAGS,"-DmaxRecDepth=9999"]]:
            with self.subTest(flags=flags),patch.object(d.ci,'FLAGS',flags):
                with self.assertRaisesRegex(ValueError,'Strict compiler flags changed'):d.validate(P,Path('/missing'),False)
    def test_failed_target_artifacts(self):
        with tempfile.TemporaryDirectory() as t:
            o=Path(t);(o/'RESULT.json').write_text(json.dumps(self.fixture()));(o/'lib').mkdir()
            (o/'lib/LocalizedTensorRestriction318.olean').write_text('static fixture, never loaded')
            for ext in d.COMPILED_SUFFIXES:
                artifact=o/'lib'/(d.MODULE+ext);artifact.write_text('static negative fixture')
                with self.assertRaisesRegex(ValueError,'Unexpected compiled artifacts'):d.validate(P,o,False)
                artifact.unlink()
            self.assertEqual(len(d.validate(P,o,False)[0]),6)
    def test_scratch_artifact_guard(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);nested=root/'nested';nested.mkdir();(root/'sample.lean').write_text('static fixture')
            d.require_no_compiled_artifacts(root)
            for ext in d.COMPILED_SUFFIXES:
                artifact=nested/('sample'+ext);artifact.write_text('static negative fixture')
                with self.assertRaisesRegex(ValueError,'Unexpected compiled artifacts'):d.require_no_compiled_artifacts(root)
                artifact.unlink()
            source=Path(d.__file__).read_text()
            self.assertIn("row=runner.bounded_memory(source,root,env,logs/(name+'.log'))\n            require_no_compiled_artifacts(root)",source)
            self.assertIn("        require_no_compiled_artifacts(root)\n        require_no_compiled_artifacts(output/'lib',MODULE)\n    ci.write_json",source)
    def test_nonacceptance(self):
        self.assertEqual(d.SECONDS,90);self.assertEqual(d.MAX_BYTES,2*1024*1024)
        s=Path(d.__file__).read_text();self.assertNotIn("'-o'",s)
        self.assertIn("'full_packet_accepted':False",s);self.assertIn("'production_source_changed':False",s)
if __name__=='__main__':unittest.main()
