#!/usr/bin/env python3
"""Static/mock tests only. This suite never starts Lean."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import diagnose_small_prime_preparation as d
ROOT=d.ci.ROOT/'quartics/quartic-318-326/proof/experiments'
P=ROOT/d.PACKET;C=ROOT/d.CONTROL_PACKET
S=(P/(d.MODULE+'.lean')).read_text();OLD=(C/(d.MODULE+'.lean')).read_text()
class Tests(unittest.TestCase):
    def fixture(self):
        i=json.loads((P/'intake.json').read_text());order=i['order'][:i['order'].index(d.MODULE)+1]
        return {'packet':d.PACKET,'packet_sha256':d.INTAKE_SHA,'commands':[{'module':n,'exit_code':124 if n==d.MODULE else 0} for n in order]}
    def prepare(self,o):
        (o/'RESULT.json').write_text(json.dumps(self.fixture()));(o/'lib').mkdir();(o/'logs').mkdir()
        (o/'lib'/(d.DEPENDENCY+'.olean')).write_text('static test fixture, never imported')
        (o/'logs'/(d.MODULE+'.log')).write_text('\nWALL_CLOCK_LIMIT_EXCEEDED\n')
    def test_exact_prefixes_and_control(self):
        prefix,chunks=d.segments(S);self.assertEqual(prefix+''.join(chunks)+d.END,S)
        cases=d.variants(S,OLD);self.assertEqual(len(cases),7);self.assertEqual(cases['historical_r14_exact_full_control'],OLD)
        for count in range(6):
            text=cases['prefix_'+str(count)]
            self.assertIn(d.PROFILE_CONTROL,text);self.assertIn('set_option stderrAsMessages false',text)
            self.assertIn('let out ← IO.getStderr',text);self.assertIn('out.flush',text)
            self.assertNotIn('sorry',text);self.assertNotIn('axiom ',text)
            for n,chunk in enumerate(chunks):self.assertEqual(chunk in text,n<count)
            self.assertEqual(text.count('set_option maxHeartbeats 0'),1)
            self.assertNotIn('set_option maxRecDepth',text)
    def test_frozen_sources(self):
        with self.assertRaisesRegex(ValueError,'Frozen source'):d.variants(S+'\n',OLD)
        with self.assertRaisesRegex(ValueError,'Historical control source'):d.variants(S,OLD+'\n')
    def test_hosted_guard(self):
        with patch.dict(d.os.environ,{},clear=True):
            with self.assertRaisesRegex(ValueError,'Hosted Actions only'):d.validate(P,Path('/missing'),C)
    def test_strict_limits(self):
        for flags in [[],['-j1','-M','6144'],['-j1','-M','6144','-Ddebug.skipKernelTC=true'],[*d.EXPECTED_FLAGS,'-DmaxRecDepth=99999']]:
            with patch.object(d.ci,'FLAGS',flags),self.assertRaisesRegex(ValueError,'Strict compiler flags'):d.validate(P,Path('/missing'),C,False)
        for key in ['SECONDS','MAX_BYTES']:
            with patch.object(d.runner.original,key,1),self.assertRaisesRegex(ValueError,'Diagnostic caps'):d.validate(P,Path('/missing'),C,False)
    def test_result_guards(self):
        with tempfile.TemporaryDirectory() as t:
            o=Path(t)
            with self.assertRaisesRegex(ValueError,'Mandatory own r15'):d.validate(P,o,C,False)
            (o/'RESULT.json').write_text('{}')
            with self.assertRaisesRegex(ValueError,'Wrong own r15'):d.validate(P,o,C,False)
            r=self.fixture();r['commands']=r['commands'][:-1];(o/'RESULT.json').write_text(json.dumps(r))
            with self.assertRaisesRegex(ValueError,'frontier changed'):d.validate(P,o,C,False)
            r=self.fixture();r['commands'][-1]['exit_code']=1;(o/'RESULT.json').write_text(json.dumps(r))
            with self.assertRaisesRegex(ValueError,'outcomes changed'):d.validate(P,o,C,False)
            r=self.fixture();r['commands'][0]['exit_code']=124;(o/'RESULT.json').write_text(json.dumps(r))
            with self.assertRaisesRegex(ValueError,'outcomes changed'):d.validate(P,o,C,False)
    def test_log_and_dependency_guards(self):
        with tempfile.TemporaryDirectory() as t:
            o=Path(t);self.prepare(o)
            self.assertEqual(len(d.validate(P,o,C,False)[0]),7)
            lp=o/'logs'/(d.MODULE+'.log');lp.write_text('error: other frontier\nWALL_CLOCK_LIMIT_EXCEEDED')
            with self.assertRaisesRegex(ValueError,'timeout log changed'):d.validate(P,o,C,False)
            lp.write_text('\nWALL_CLOCK_LIMIT_EXCEEDED\n');(o/'lib'/(d.DEPENDENCY+'.olean')).unlink()
            with self.assertRaisesRegex(ValueError,'dependency missing'):d.validate(P,o,C,False)
    def test_failed_target_all_artifact_guards(self):
        with tempfile.TemporaryDirectory() as t:
            o=Path(t);self.prepare(o)
            for suffix in d.COMPILED_SUFFIXES:
                p=o/'lib'/(d.MODULE+suffix);p.write_text('static negative fixture')
                with self.assertRaisesRegex(ValueError,'Unexpected compiled'):d.validate(P,o,C,False)
                p.unlink()
    def test_nested_scratch_artifacts(self):
        with tempfile.TemporaryDirectory() as t:
            o=Path(t);(o/'nested').mkdir()
            for suffix in d.COMPILED_SUFFIXES:
                p=o/'nested'/('example'+suffix);p.write_text('static negative fixture')
                with self.assertRaisesRegex(ValueError,'Unexpected compiled'):d.no_compiled(o)
                p.unlink()
    def test_source_binding_guard(self):
        real=d.sha
        with patch.object(d,'sha',lambda p:'bad' if p.name==d.MODULE+'.lean' else real(p)):
            with self.assertRaisesRegex(ValueError,'Source binding changed'):d.validate(P,Path('/missing'),C,False)
    def test_packet_metadata_guard(self):
        real=d.sha
        for n in ['intake.json','APPLICATION.json']:
            with patch.object(d,'sha',lambda p:'bad' if p.name==n else real(p)):
                with self.assertRaisesRegex(ValueError,'Frozen packet changed'):d.validate(P,Path('/missing'),C,False)
    def test_runner_binding_guard(self):
        real=d.sha
        with patch.object(d,'sha',lambda p:'bad' if p==Path(d.runner.__file__) else real(p)):
            with self.assertRaisesRegex(ValueError,'runner implementation'):d.validate(P,Path('/missing'),C,False)
    def test_workflow_exact_lane_and_upload(self):
        workflow=(Path(__file__).resolve().parent.parent/'.github/workflows/progress-experiments.yml').read_text()
        self.assertEqual(workflow.count('python -B scripts/test_small_prime_diagnostic.py'),1)
        self.assertEqual(workflow.count('lake env python -B ../../../../scripts/diagnose_small_prime_preparation.py "$PACKET"'),1)
        self.assertIn("if: always() && matrix.packet == '"+d.PACKET+"'",workflow)
        self.assertIn('scratch-small-prime-preparation/',workflow)
        self.assertIn('--seconds 180',workflow);self.assertIn('cancel-in-progress: false',workflow)
    def test_no_acceptance_or_output_artifacts(self):
        s=Path(d.__file__).read_text();self.assertNotIn("'-o'",s);self.assertNotIn('skipKernelTC=true',s)
        self.assertEqual(d.SECONDS,90);self.assertEqual(d.MAX_BYTES,2*1024*1024)
        self.assertIn('7*SECONDS',s);self.assertIn('630 seconds',s)
        self.assertIn("'production_source_changed':False",s);self.assertIn("'production_limits_changed':False",s)
        self.assertIn('no_compiled(root);no_compiled(output/\'lib\', MODULE)\n            source',s)
        self.assertIn('row = runner.bounded_memory(source, root, env, logs/(name+\'.log\'))\n            no_compiled(root);no_compiled(output/\'lib\', MODULE)',s)
if __name__=='__main__':unittest.main()
