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
        cases=d.variants(S,OLD);self.assertEqual(len(cases),5)
        for text in cases.values():
            self.assertIn(d.PROFILE_CONTROL,text);self.assertIn('set_option stderrAsMessages false',text)
            self.assertIn('let out ← IO.getStderr',text);self.assertIn('out.flush',text)
            self.assertNotIn('sorry',text);self.assertNotIn('axiom ',text)
            self.assertEqual(text.count('set_option maxHeartbeats 0'),1)
            self.assertNotIn('set_option maxRecDepth',text)
        for chunk in chunks[:3]:self.assertIn(chunk,cases['exact_prefix3_sparse_profile'])
    def test_frozen_sources(self):
        with self.assertRaisesRegex(ValueError,'Frozen source'):d.variants(S+'\n',OLD)
        with self.assertRaisesRegex(ValueError,'Historical r15 source'):d.variants(S,OLD+'\n')
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
            with self.assertRaisesRegex(ValueError,'Mandatory own r16'):d.validate(P,o,C,False)
            (o/'RESULT.json').write_text('{}')
            with self.assertRaisesRegex(ValueError,'Wrong own r16'):d.validate(P,o,C,False)
            r=self.fixture();r['commands']=r['commands'][:-1];(o/'RESULT.json').write_text(json.dumps(r))
            with self.assertRaisesRegex(ValueError,'frontier changed'):d.validate(P,o,C,False)
            r=self.fixture();r['commands'][-1]['exit_code']=0;(o/'RESULT.json').write_text(json.dumps(r))
            with self.assertRaisesRegex(ValueError,'outcomes changed'):d.validate(P,o,C,False)
            r=self.fixture();r['commands'][0]['exit_code']=124;(o/'RESULT.json').write_text(json.dumps(r))
            with self.assertRaisesRegex(ValueError,'outcomes changed'):d.validate(P,o,C,False)
    def test_log_and_dependency_guards(self):
        with tempfile.TemporaryDirectory() as t:
            o=Path(t);self.prepare(o)
            self.assertEqual(len(d.validate(P,o,C,False)[0]),5)
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
        self.assertIn('scratch-small-prime-decidable/',workflow)
        self.assertIn('--seconds 180',workflow);self.assertIn('cancel-in-progress: false',workflow)
    def test_no_acceptance_or_output_artifacts(self):
        s=Path(d.__file__).read_text();self.assertNotIn("'-o'",s);self.assertNotIn('skipKernelTC=true',s)
        self.assertEqual(d.SECONDS,90);self.assertEqual(d.MAX_BYTES,2*1024*1024)
        self.assertIn('5*SECONDS',s);self.assertIn('450 seconds',s)
        self.assertIn("'production_source_changed':False",s);self.assertIn("'production_limits_changed':False",s)
        self.assertIn('no_compiled(root);no_compiled(output/\'lib\', MODULE)\n            source',s)
        self.assertIn('row = runner.bounded_memory(source, root, env, logs/(name+\'.log\'))\n            no_compiled(root);no_compiled(output/\'lib\', MODULE)',s)
    def test_exit1_requires_own_error(self):
        with tempfile.TemporaryDirectory() as t:
            o=Path(t);self.prepare(o);r=self.fixture();r['commands'][-1]['exit_code']=1;(o/'RESULT.json').write_text(json.dumps(r))
            with self.assertRaisesRegex(ValueError,'lacks hard-error'):d.validate(P,o,C,False)
            (o/'logs'/(d.MODULE+'.log')).write_text(d.MODULE+'.lean:99:1: error: synthetic negative fixture')
            self.assertEqual(len(d.validate(P,o,C,False)[0]),5)
    def test_wrong_packet_and_historical_result(self):
        with tempfile.TemporaryDirectory() as t:
            o=Path(t);self.prepare(o);r=self.fixture();r['packet']=d.CONTROL_PACKET;(o/'RESULT.json').write_text(json.dumps(r))
            with self.assertRaisesRegex(ValueError,'Wrong own r16'):d.validate(P,o,C,False)
        with self.assertRaisesRegex(ValueError,'Wrong packet'):d.validate(C,Path('/missing'),P,False)
    def test_original_context_source_inverse(self):
        import re
        _,chunks=d.segments(S);cases=d.variants(S,OLD)
        strip=lambda text:re.sub(r'(?m)^ +run_tac do\n +let out ← IO.getStderr\n +out.putStrLn "SMALL_PRIME_TACTIC_[A-Z_0-9]+"\n +out.flush\n','',text)
        self.assertIn(chunks[2],strip(cases['exact_prefix3_tactic_markers']))
        text=strip(cases['split_unit_value_convert_prefix3'])
        for p,e,sub,term in [(2,4,'₂','1+8*k₂'),(3,2,'₃','1+3*k₃'),(17,2,'₁₇','8+17*k₁₇')]:
            text=text.replace(f'    have hu{sub} : ¬({p}:ℤ)∣({term}) := by omega\n    have hv{sub} := value_scaled_unit {p} {e} ({term}) hu{sub}\n    convert hv{sub} using 1 <;> norm_num\n',f'    convert value_scaled_unit {p} {e} ({term}) (by omega) using 1 <;> norm_num\n')
        self.assertIn(chunks[2],text)
    def test_sparse_profiles_and_distinct_controls(self):
        cases=d.variants(S,OLD)
        for text in cases.values():self.assertIn('profiler.threshold 10',text);self.assertIn('`profiler.threshold (0 : Nat)',text)
        self.assertIn('Int.pow_emod',cases['historical_r15_prefix3_sparse_profile'])
        text=cases['abstract_three_unit_control'];self.assertIn('BEFORE_diagnostic_abstract_units',text);self.assertNotIn('BEFORE_integerA_shapes',text)
        for term in ['1+8*k₂','1+3*k₃','8+17*k₁₇']:self.assertIn(term,text)
    def test_all_final_pins(self):
        self.assertEqual(d.sha(P/'intake.json'),d.INTAKE_SHA);self.assertEqual(d.sha(P/'APPLICATION.json'),d.APPLICATION_SHA)
        self.assertNotIn('PENDING',Path(d.__file__).read_text())
if __name__=='__main__':unittest.main()
