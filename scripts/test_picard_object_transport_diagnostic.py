#!/usr/bin/env python3
"""Static generation/guard tests only: no local Lean or real runner execution."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import diagnose_picard_object_transport as d
from test_picard_overlap_fragments_diagnostic import Fragments

class ObjectTransport(unittest.TestCase):
    def packet(self):return d.ci.ROOT/'quartics/quartic-318-326/proof/experiments'/d.PACKET
    def source(self):return (self.packet()/(d.MODULE+'.lean')).read_text()
    def fixture(self,out):
        Fragments().fixture(out)
        cases,result_sha,log_sha,prior_sha=d.fragments.validate(self.packet(),out,hosted=False)
        prior=out/'scratch-picard-overlap-fragments';prior.mkdir();rows=[]
        for index,(name,text) in enumerate(cases.items()):
            (prior/(name+'.lean.txt')).write_text(text)
            log=('PICARD_FRAGMENT_'+name+'_COMMAND_END' if index<2 else
                 'PICARD_FRAGMENT_B_BODY_ENTER\nPICARD_FRAGMENT_B_BODY_EXIT\nSCRATCH_WALL_LIMIT' if index==2 else
                 'PICARD_FRAGMENT_ASSEMBLED_AFTER_A_COMMAND_END\nPICARD_SITE_BODY_00_ENTER_reconstructed_actual_overlap\nPICARD_SITE_BODY_01_EXIT_reconstructed_actual_overlap\nSCRATCH_WALL_LIMIT')
            (prior/(name+'.log')).write_text(log)
            rows.append(dict(variant=name,source_sha256=hashlib.sha256(text.encode()).hexdigest(),
                             admitted=False,proof_acceptance=False,contains_sorry=False,
                             exact_A_equation_is_extra_diagnostic_input=(index==2),
                             exit_code=0 if index<2 else -9,limit=None if index<2 else 'SCRATCH_WALL_LIMIT'))
        rec=dict(scope='NON_ADMITTED_EXACT_PICARD_A_B_ASSEMBLED_ONLY',packet=d.PACKET,
                 packet_intake_sha256=d.isolation.INTAKE_SHA,packet_application_sha256=d.isolation.APPLICATION_SHA,
                 original_source_sha256=d.isolation.SOURCE_SHA,full_result_sha256=result_sha,
                 production_log_sha256=log_sha,prior_isolation_result_sha256=prior_sha,
                 seconds_per_probe=d.SECONDS,bytes_per_probe=d.MAX_BYTES,
                 full_packet_accepted=False,baseline_or_experiment_accepted=False,writes_olean=False,
                 production_source_changed=False,production_limits_changed=False,variants=rows)
        (prior/'DIAGNOSTIC.json').write_text(json.dumps(rec));return prior,rec
    def test_exact_three_cases(self):
        cases=d.variants(self.source());self.assertEqual(list(cases),d.NAMES)
        for name,text in cases.items():
            self.assertNotIn('sorry',text);self.assertNotIn('axiom ',text)
            self.assertNotIn(d.isolation.FORBIDDEN_MARKER,text)
            self.assertTrue(text.endswith(d.isolation.END));self.assertIn(d.marker(name),text)
    def test_exact_original_statement_native_A_and_equality(self):
        prefix,original,statement,native,inner,a,b,old=d.fragments.fragments(self.source())
        cases=d.variants(self.source());assembled=cases[d.NAMES[2]]
        self.assertIn(statement+' := by\n',assembled);self.assertIn(a,assembled)
        self.assertIn('exact ReconstructedOverlapCompatibility318.comparison_eq '+d.ARGS,assembled)
        self.assertIn(d.DTYPED,assembled);self.assertIn(d.GENERIC,assembled)
        self.assertNotIn('original_overlap_of_object_eq (baseMap R S)',assembled)
        typed=cases[d.NAMES[0]]
        self.assertIn('hObject L.object',typed);self.assertIn('hComparison τ\n    hA',typed)
        self.assertIn('(hA :\n'+native+')',typed)
        self.assertTrue(all(t.startswith(prefix) for t in cases.values()))
    def test_no_premise_leak(self):
        for name,text in d.variants(self.source()).items():
            for token in ['(hObject :','(hComparison :','(hA :']:
                self.assertEqual(token in text,name==d.NAMES[0])
    def test_resource_and_trust_unchanged(self):
        old=[x for x in self.source().splitlines() if x.startswith('set_option ') and 'profiler' not in x]
        for text in d.variants(self.source()).values():
            self.assertEqual([x for x in text.splitlines() if x.startswith('set_option ') and 'profiler' not in x],old)
        self.assertEqual(d.SECONDS,90);self.assertEqual(d.MAX_BYTES,2097152)
        self.assertEqual(d.ci.FLAGS,['-j1','-M','6144','-Ddebug.skipKernelTC=false'])
    def test_source_mutation_and_hosted_guard(self):
        with self.assertRaisesRegex(ValueError,'Frozen source'):d.variants(self.source()+'\n')
        with patch.dict(d.os.environ,{},clear=True):
            with self.assertRaisesRegex(ValueError,'Hosted Actions only'):d.validate(self.packet(),Path('/not-used'))
    def test_valid_fixture(self):
        with tempfile.TemporaryDirectory() as t:
            out=Path(t);self.fixture(out);self.assertEqual(len(d.validate(self.packet(),out,hosted=False)[0]),3)
    def test_missing_prior(self):
        with tempfile.TemporaryDirectory() as t:
            out=Path(t);Fragments().fixture(out)
            with self.assertRaisesRegex(ValueError,'Mandatory prior fragments'):d.validate(self.packet(),out,hosted=False)
    def test_identity_and_admission_guards(self):
        with tempfile.TemporaryDirectory() as t:
            out=Path(t);prior,rec=self.fixture(out);p=prior/'DIAGNOSTIC.json'
            for key in ['packet','packet_intake_sha256','packet_application_sha256','original_source_sha256','full_result_sha256','production_log_sha256','prior_isolation_result_sha256','seconds_per_probe','bytes_per_probe']:
                bad=dict(rec);bad[key]='wrong';p.write_text(json.dumps(bad))
                with self.assertRaisesRegex(ValueError,'binding changed'):d.validate(self.packet(),out,hosted=False)
            for key in ['full_packet_accepted','baseline_or_experiment_accepted','writes_olean','production_source_changed','production_limits_changed']:
                bad=dict(rec);bad[key]=True;p.write_text(json.dumps(bad))
                with self.assertRaisesRegex(ValueError,'boundary changed'):d.validate(self.packet(),out,hosted=False)
    def test_specimen_guards(self):
        with tempfile.TemporaryDirectory() as t:
            out=Path(t);prior,rec=self.fixture(out)
            for row in rec['variants']:
                p=prior/(row['variant']+'.lean.txt');raw=p.read_bytes();p.write_bytes(raw+b'\n')
                with self.assertRaisesRegex(ValueError,'specimen changed'):d.validate(self.packet(),out,hosted=False)
                p.write_bytes(raw)
    def test_outcome_and_premise_guards(self):
        with tempfile.TemporaryDirectory() as t:
            out=Path(t);prior,rec=self.fixture(out);p=prior/'DIAGNOSTIC.json'
            for index in range(4):
                for key,value,pattern in [('exit_code',1,'outcome changed'),('admitted',True,'admission detected'),('contains_sorry',True,'placeholder'),('exact_A_equation_is_extra_diagnostic_input',index!=2,'premise classification')]:
                    bad=json.loads(json.dumps(rec));bad['variants'][index][key]=value;p.write_text(json.dumps(bad))
                    with self.assertRaisesRegex(ValueError,pattern):d.validate(self.packet(),out,hosted=False)
    def test_markers(self):
        with tempfile.TemporaryDirectory() as t:
            out=Path(t);prior,rec=self.fixture(out)
            for index,row in enumerate(rec['variants']):
                p=prior/(row['variant']+'.log');raw=p.read_bytes();p.write_text('SCRATCH_WALL_LIMIT')
                with self.assertRaisesRegex(ValueError,'end missing' if index<2 else 'frontier changed'):d.validate(self.packet(),out,hosted=False)
                p.write_bytes(raw)
    def test_no_promotion_or_local_main(self):
        text=Path(d.__file__).read_text();self.assertNotIn("'-o'",text)
        for token in ["'writes_olean':False","'production_source_changed':False",'admitted=False,proof_acceptance=False',"dir=os.environ['RUNNER_TEMP']","if __name__=='__main__':main()","'maximum_additional_scratch_wall_seconds':3*SECONDS"]:self.assertIn(token,text)

if __name__=='__main__':unittest.main()
