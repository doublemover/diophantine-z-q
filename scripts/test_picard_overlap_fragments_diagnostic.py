#!/usr/bin/env python3
"""Static source/guard tests only. No Lean or real diagnostic runner invocation."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import diagnose_picard_overlap_fragments as d
from test_picard_reconstructed_overlap_diagnostic import PicardDiagnostics

class Fragments(unittest.TestCase):
    def packet(self):return d.ci.ROOT/'quartics/quartic-318-326/proof/experiments'/d.PACKET
    def source(self):return (self.packet()/(d.MODULE+'.lean')).read_text()
    def fixture(self,out):
        PicardDiagnostics().fixture(out)
        cases,result_sha,log_sha=d.isolation.validate(self.packet(),out,hosted=False)
        prior=out/'scratch-picard-reconstructed-overlap';prior.mkdir();rows=[]
        for index,(name,text) in enumerate(cases.items()):
            (prior/(name+'.lean.txt')).write_text(text)
            log=('PICARD_NONADMITTED_'+name+'_COMMAND_END' if index<2 else
                'PICARD_SITE_BODY_00_ENTER_reconstructed_actual_overlap\n'
                'PICARD_SITE_BODY_01_EXIT_reconstructed_actual_overlap\nSCRATCH_WALL_LIMIT')
            (prior/(name+'.log')).write_text(log)
            rows.append(dict(variant=name,source_sha256=hashlib.sha256(text.encode()).hexdigest(),
                admitted=False,proof_acceptance=False,contains_sorry=(index==1),
                exit_code=0 if index<2 else -9,limit=None if index<2 else 'SCRATCH_WALL_LIMIT'))
        rec=dict(scope='NON_ADMITTED_PICARD_HELPER_ISOLATION_ONLY',packet=d.PACKET,
            packet_intake_sha256=d.isolation.INTAKE_SHA,packet_application_sha256=d.isolation.APPLICATION_SHA,
            original_source_sha256=d.isolation.SOURCE_SHA,full_result_sha256=result_sha,
            production_log_sha256=log_sha,seconds_per_probe=d.SECONDS,bytes_per_probe=d.MAX_BYTES,
            full_packet_accepted=False,baseline_or_experiment_accepted=False,writes_olean=False,
            production_source_changed=False,production_limits_changed=False,variants=rows)
        (prior/'DIAGNOSTIC.json').write_text(json.dumps(rec));return prior,rec
    def test_exact_four_cases(self):
        cases=d.variants(self.source());self.assertEqual(list(cases),d.NAMES)
        for name,text in cases.items():
            self.assertNotIn('sorry',text);self.assertNotIn('axiom ',text)
            self.assertNotIn(d.isolation.FORBIDDEN_MARKER,text)
            self.assertNotIn('lemma original_overlap :',text)
            self.assertTrue(text.endswith(d.isolation.END))
            self.assertIn('PICARD_FRAGMENT_'+name+'_COMMAND_END',text)
    def test_exact_source_slices_and_assembly(self):
        prefix,original,statement,native,inner,a,b,assembled=d.fragments(self.source())
        self.assertTrue(self.source().startswith(prefix));self.assertIn(original,self.source())
        self.assertIn(statement+' := by\n',original)
        self.assertIn('('+inner+')',original)
        self.assertEqual(assembled.replace('('+d.A_CALL+')','('+inner+')'),original)
        self.assertIn('  exact '+inner+'\n',a)
        self.assertIn('    hA\n',b)
        self.assertIn('ReconstructedOverlapCompatibility318.comparison_transport',b)
        self.assertIn('ReconstructedOverlapCompatibility318.namedComparison',native)
    def test_no_added_hypothesis_except_B(self):
        cases=d.variants(self.source())
        for name,text in cases.items():
            self.assertEqual('(hA :' in text,name==d.NAMES[2])
        self.assertIn('private lemma '+d.A_NAME,cases[d.NAMES[3]])
        self.assertIn('private lemma reconstructed_actual_overlap',cases[d.NAMES[3]])
        self.assertIn('('+d.A_CALL+')',cases[d.NAMES[3]])
        self.assertNotIn('private lemma '+d.B_NAME,cases[d.NAMES[3]])
    def test_resource_and_trust_options(self):
        old=[x for x in self.source().splitlines() if x.startswith('set_option ') and 'profiler' not in x]
        for text in d.variants(self.source()).values():
            self.assertEqual([x for x in text.splitlines() if x.startswith('set_option ') and 'profiler' not in x],old)
        self.assertEqual(d.SECONDS,90);self.assertEqual(d.MAX_BYTES,2097152)
        self.assertEqual(d.ci.FLAGS,['-j1','-M','6144','-Ddebug.skipKernelTC=false'])
    def test_source_mutation(self):
        with self.assertRaisesRegex(ValueError,'Frozen source'):d.variants(self.source()+'\n')
    def test_prior_missing_and_hosted_guard(self):
        with patch.dict(d.os.environ,{},clear=True):
            with self.assertRaisesRegex(ValueError,'Hosted Actions only'):d.validate(self.packet(),Path('/not-used'))
        with tempfile.TemporaryDirectory() as t:
            out=Path(t);PicardDiagnostics().fixture(out)
            with self.assertRaisesRegex(ValueError,'Mandatory prior isolation'):d.validate(self.packet(),out,hosted=False)
    def test_valid_static_fixture(self):
        with tempfile.TemporaryDirectory() as t:
            out=Path(t);self.fixture(out);self.assertEqual(len(d.validate(self.packet(),out,hosted=False)[0]),4)
    def test_binding_and_admission_guards(self):
        with tempfile.TemporaryDirectory() as t:
            out=Path(t);prior,rec=self.fixture(out);p=prior/'DIAGNOSTIC.json'
            for key in ['packet_intake_sha256','packet_application_sha256','original_source_sha256','full_result_sha256','production_log_sha256']:
                bad=dict(rec);bad[key]='wrong';p.write_text(json.dumps(bad))
                with self.assertRaisesRegex(ValueError,'binding changed'):d.validate(self.packet(),out,hosted=False)
            for key in ['full_packet_accepted','baseline_or_experiment_accepted','writes_olean','production_source_changed','production_limits_changed']:
                bad=dict(rec);bad[key]=True;p.write_text(json.dumps(bad))
                with self.assertRaisesRegex(ValueError,'boundary changed'):d.validate(self.packet(),out,hosted=False)
    def test_prior_specimen_guards(self):
        with tempfile.TemporaryDirectory() as t:
            out=Path(t);prior,rec=self.fixture(out)
            for name in d.isolation.variants(self.source()):
                p=prior/(name+'.lean.txt');original=p.read_text();p.write_text(original+'\n')
                with self.assertRaisesRegex(ValueError,'specimen changed'):d.validate(self.packet(),out,hosted=False)
                p.write_text(original)
    def test_outcome_and_placeholder_guards(self):
        with tempfile.TemporaryDirectory() as t:
            out=Path(t);prior,rec=self.fixture(out);p=prior/'DIAGNOSTIC.json'
            for index in range(3):
                bad=json.loads(json.dumps(rec));bad['variants'][index]['exit_code']=1;p.write_text(json.dumps(bad))
                with self.assertRaisesRegex(ValueError,'outcome changed'):d.validate(self.packet(),out,hosted=False)
            bad=json.loads(json.dumps(rec));bad['variants'][1]['contains_sorry']=False;p.write_text(json.dumps(bad))
            with self.assertRaisesRegex(ValueError,'placeholder classification'):d.validate(self.packet(),out,hosted=False)
            bad=json.loads(json.dumps(rec));bad['variants'][2]['proof_acceptance']=True;p.write_text(json.dumps(bad))
            with self.assertRaisesRegex(ValueError,'admission detected'):d.validate(self.packet(),out,hosted=False)
    def test_prior_marker_guards(self):
        with tempfile.TemporaryDirectory() as t:
            out=Path(t);prior,_=self.fixture(out);p=prior/'exact_unchanged_helper.log';p.write_text('SCRATCH_WALL_LIMIT')
            with self.assertRaisesRegex(ValueError,'boundary changed'):d.validate(self.packet(),out,hosted=False)
    def test_no_local_entry_or_output_promotion(self):
        text=Path(d.__file__).read_text();self.assertNotIn("'-o'",text)
        for token in ["'writes_olean':False","'production_source_changed':False",'admitted=False,proof_acceptance=False',"dir=os.environ['RUNNER_TEMP']","if __name__=='__main__':main()"]:self.assertIn(token,text)

if __name__=='__main__':unittest.main()
