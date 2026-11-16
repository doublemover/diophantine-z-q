#!/usr/bin/env python3
"""Static/mocked guard tests only. Subprocess entry points are blocked; never runs Lean."""
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import diagnose_prepared_anchor_elaboration as d
P=Path(os.environ.get('ANCHOR_DIAGNOSTIC_TEST_PACKET',str(d.ci.ROOT/'quartics/quartic-318-326/proof/experiments'/d.PACKET)))
S=(P/(d.MODULE+'.lean')).read_text()
WORKFLOW=Path(os.environ.get('ANCHOR_DIAGNOSTIC_TEST_WORKFLOW',str(d.ci.ROOT/'.github/workflows/progress-experiments.yml')))

class Tests(unittest.TestCase):
    def setUp(self):
        for name in ['Popen','run','call','check_call','check_output']:
            p=patch('subprocess.'+name,side_effect=AssertionError('No subprocess allowed in static tests'));p.start();self.addCleanup(p.stop)
    def fixture(self):
        i=json.loads((P/'intake.json').read_text());order=i['order'][:i['order'].index(d.MODULE)+1]
        return {'status':'FAILED','packet':d.PACKET,'packet_sha256':d.INTAKE_SHA,'commands':[{'module':n,'exit_code':1 if n==d.MODULE else 0} for n in order]}
    def prepare(self,o):
        r=self.fixture();(o/'RESULT.json').write_text(json.dumps(r));(o/'lib').mkdir();(o/'logs').mkdir()
        for row in r['commands'][:-1]:(o/'lib'/(row['module']+'.olean')).write_text('Static fixture; never imported by Lean')
        (o/'logs'/(d.MODULE+'.log')).write_text('/fixture/'+d.FAILURE+'\n')
    def test_exact_single_scoped_specimen(self):
        text=d.specimen(S);self.assertEqual(text.replace(d.SCOPE,'',1),S);self.assertEqual(text.count(d.SCOPE),1)
        self.assertEqual(d.digest(text),d.SCRATCH_SHA);self.assertNotIn('sorry',text);self.assertNotIn('axiom ',text)
        self.assertNotIn('profiler',text);self.assertEqual(text.count('set_option maxHeartbeats 1000000'),1)
    def test_no_specimen_source_drift(self):
        with self.assertRaisesRegex(ValueError,'Frozen target'):d.specimen(S+'\n')
    def test_hosted_guard(self):
        with patch.dict(d.os.environ,{},clear=True),self.assertRaisesRegex(ValueError,'Hosted Actions only'):d.validate(P,Path('/missing'))
    def test_runner_and_limits(self):
        actual=d.sha
        with patch.object(d,'sha',lambda p:'bad' if p==Path(d.runner.__file__) else actual(p)),self.assertRaisesRegex(ValueError,'runner changed'):d.validate(P,Path('/missing'),False)
        for key in ['SECONDS','MAX_BYTES']:
            with patch.object(d.runner.original,key,1),self.assertRaisesRegex(ValueError,'scratch caps changed'):d.validate(P,Path('/missing'),False)
        for flags in [[],['-j1','-M','6144'],['-j1','-M','6144','-Ddebug.skipKernelTC=true']]:
            with patch.object(d.ci,'FLAGS',flags),self.assertRaisesRegex(ValueError,'Strict compiler flags'):d.validate(P,Path('/missing'),False)
    def test_metadata_and_source_guards(self):
        actual=d.sha
        for n in ['intake.json','APPLICATION.json',d.MODULE+'.lean']:
            with patch.object(d,'sha',lambda p:'bad' if p.name==n else actual(p)),self.assertRaises(ValueError):d.validate(P,Path('/missing'),False)
        with self.assertRaisesRegex(ValueError,'Wrong activation'):d.validate(P.parent/'wrong',Path('/missing'),False)
    def test_fresh_result_required(self):
        with tempfile.TemporaryDirectory() as t:
            o=Path(t)
            with self.assertRaisesRegex(ValueError,'Fresh own normal'):d.validate(P,o,False)
            (o/'RESULT.json').write_text('{}')
            with self.assertRaisesRegex(ValueError,'identity changed'):d.validate(P,o,False)
    def test_normal_outcome_guards(self):
        with tempfile.TemporaryDirectory() as t:
            o=Path(t);self.prepare(o)
            for mutation in ['success','historical','missing_last','earlier_failure','timeout']:
                r=self.fixture()
                if mutation=='success':r['status']='PASS'
                if mutation=='historical':r['packet']='forward-original-weighted-weyl-r22-replay-r34'
                if mutation=='missing_last':r['commands'].pop()
                if mutation=='earlier_failure':r['commands'][0]['exit_code']=1
                if mutation=='timeout':r['commands'][-1]['exit_code']=124
                (o/'RESULT.json').write_text(json.dumps(r))
                with self.assertRaises(ValueError):d.validate(P,o,False)
    def test_exact_error_and_dependency(self):
        with tempfile.TemporaryDirectory() as t:
            o=Path(t);self.prepare(o);text,e=d.validate(P,o,False)
            self.assertEqual(text,d.specimen(S));self.assertEqual(len(e['successful_prefix_modules']),117)
            log=o/'logs'/(d.MODULE+'.log');log.write_text('some unrelated error')
            with self.assertRaisesRegex(ValueError,'unknown-free-variable failure absent'):d.validate(P,o,False)
            log.write_text(d.FAILURE);(o/'lib'/(d.DEPENDENCY+'.olean')).unlink()
            with self.assertRaisesRegex(ValueError,'predecessor missing'):d.validate(P,o,False)
    def test_all_failed_target_artifacts_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            o=Path(t);self.prepare(o)
            for suffix in d.COMPILED_SUFFIXES:
                p=o/'lib'/(d.MODULE+suffix);p.write_text('forbidden fixture')
                with self.assertRaisesRegex(ValueError,'Unexpected compiled'):d.validate(P,o,False)
                p.unlink()
    def test_nested_scratch_artifacts_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            o=Path(t);(o/'nested').mkdir()
            for suffix in d.COMPILED_SUFFIXES:
                p=o/'nested'/('bad'+suffix);p.write_text('forbidden fixture')
                with self.assertRaisesRegex(ValueError,'Unexpected compiled'):d.no_compiled(o)
                p.unlink()
    def test_skip_is_explicit_and_runs_no_probe(self):
        with tempfile.TemporaryDirectory() as t,patch.object(d.ci,'ROOT',Path(t)),patch.dict(d.os.environ,{'GITHUB_ACTIONS':'true','RUNNER_TEMP':t}),patch('sys.argv',['diagnostic',d.PACKET]),patch.object(d.runner,'bounded_memory',side_effect=AssertionError('Unexpected probe')):
            d.main();r=json.loads((Path(t)/'build/progress-experiments'/d.PACKET/d.LABEL/'DIAGNOSTIC.json').read_text())
            self.assertEqual(r['status'],'SKIPPED');self.assertFalse(r['probe_executed']);self.assertFalse(r['proof_acceptance']);self.assertIn('reason',r)
    def test_workflow_exact_lane_and_upload(self):
        w=WORKFLOW.read_text();self.assertEqual(w.count('python -B scripts/test_prepared_anchor_elaboration_diagnostic.py'),1)
        self.assertEqual(w.count('lake env python -B ../../../../scripts/diagnose_prepared_anchor_elaboration.py "$PACKET"'),1)
        self.assertIn("if: always() && steps.dependency_sources.outcome == 'success' && matrix.packet == '"+d.PACKET+"'",w)
        self.assertIn('scratch-prepared-anchor-elaboration/',w);self.assertIn('--seconds 180',w);self.assertIn('cancel-in-progress: false',w)
        self.assertIn("      - 'scripts/diagnose_prepared_anchor_elaboration.py'",w)
        self.assertIn("      - 'scripts/test_prepared_anchor_elaboration_diagnostic.py'",w)
    def test_no_outputs_or_acceptance(self):
        s=Path(d.__file__).read_text();self.assertNotIn("'-o'",s);self.assertNotIn('skipKernelTC=true',s)
        self.assertEqual(d.SECONDS,90);self.assertEqual(d.MAX_BYTES,2*1024*1024)
        self.assertEqual(s.count('row=runner.bounded_memory('),1);self.assertIn("'proof_acceptance':False",s)
        self.assertIn("'production_source_changed':False",s);self.assertIn("'production_limits_changed':False",s)
    def test_exact_current_pins(self):
        self.assertEqual(d.sha(P/'intake.json'),d.INTAKE_SHA);self.assertEqual(d.sha(P/'APPLICATION.json'),d.APPLICATION_SHA)
        self.assertEqual(d.digest(S),d.SOURCE_SHA)

if __name__=='__main__':unittest.main()
