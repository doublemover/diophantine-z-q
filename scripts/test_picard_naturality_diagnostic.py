#!/usr/bin/env python3
"""Source/static/mock tests only. Never invokes Lean or a real compiler process."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import diagnose_picard_naturality as d
import test_picard_object_transport_diagnostic as old_tests

class Naturality(unittest.TestCase):
    def packet(self):return d.ci.ROOT/'quartics/quartic-318-326/proof/experiments'/d.PACKET
    def source(self):return (self.packet()/(d.MODULE+'.lean')).read_text()
    def test_exact_two_cases(self):
        cases=d.variants(self.source());self.assertEqual(list(cases),d.NAMES)
        for n,t in cases.items():
            self.assertTrue(t.endswith(d.isolation.END));self.assertIn(d.marker(n),t)
            for token in ['sorry','axiom ','(hObject :','(hComparison :','(hA :',d.isolation.FORBIDDEN_MARKER]:
                self.assertNotIn(token,t)
    def test_assembled_exact_original_statement(self):
        prefix,original,statement,native,inner,a,b,old=d.fragments.fragments(self.source())
        cases=d.variants(self.source());assembled=cases[d.NAMES[1]]
        self.assertIn(statement+' := by\n',assembled);self.assertIn(a,assembled)
        self.assertIn(d.HCMP,assembled);self.assertIn(d.CISO,assembled)
        self.assertIn(d.AV,assembled);self.assertIn(d.AW,assembled)
        self.assertNotIn('original_overlap_of_object_eq (baseMap R S)',assembled)
        self.assertTrue(all(t.startswith(prefix) for t in cases.values()))
    def test_actual_naturality_components(self):
        self.assertIn(').hom.naturality c',d.NAT_GENERIC)
        self.assertIn(').inv.naturality c',d.NAT_GENERIC)
        self.assertIn('CanonicalSheafOverlap318.actual CanonicalSheafOverlap318.overlap',d.NAT_GENERIC)
        self.assertNotIn('cases ',d.NAT_GENERIC+d.TRANSFER_GENERIC)
    def test_resources_unchanged(self):
        options=[x for x in self.source().splitlines() if x.startswith('set_option ') and 'profiler' not in x]
        for t in d.variants(self.source()).values():
            self.assertEqual([x for x in t.splitlines() if x.startswith('set_option ') and 'profiler' not in x],options)
        self.assertEqual(d.SECONDS,90);self.assertEqual(d.MAX_BYTES,2097152)
        self.assertEqual(d.ci.FLAGS,['-j1','-M','6144','-Ddebug.skipKernelTC=false'])
    def test_source_change_rejected(self):
        with self.assertRaisesRegex(ValueError,'Frozen source'):d.variants(self.source()+'\n')
    def test_hosted_guard(self):
        with patch.dict(d.os.environ,{},clear=True):
            with self.assertRaisesRegex(ValueError,'Hosted Actions only'):
                d.validate(self.packet(),Path('/not-used'))
    def test_authentic_history(self):
        self.assertEqual(d.history(self.source()),d.HISTORY_SHA)
    def test_history_byte_change(self):
        with tempfile.TemporaryDirectory() as t:
            p=Path(t)/'history.json';p.write_bytes(d.HISTORY.read_bytes()+b'\n')
            with self.assertRaisesRegex(ValueError,'bundle changed'):d.history(self.source(),p)
    def mutated(self,modify,pattern):
        with tempfile.TemporaryDirectory() as t:
            j=json.loads(d.HISTORY.read_text());modify(j);p=Path(t)/'history.json';p.write_text(json.dumps(j))
            with patch.object(d,'HISTORY_SHA',hashlib.sha256(p.read_bytes()).hexdigest()):
                with self.assertRaisesRegex(ValueError,pattern):d.history(self.source(),p)
    def test_history_identity(self):
        self.mutated(lambda j:j['artifact'].__setitem__('id',1),'official artifact changed')
        self.mutated(lambda j:j['artifact'].__setitem__('digest','wrong'),'artifact digest changed')
    def test_history_bindings(self):
        for key in ['packet','packet_intake_sha256','packet_application_sha256','original_source_sha256','seconds_per_probe','bytes_per_probe']:
            self.mutated(lambda j,k=key:j['diagnostic'].__setitem__(k,'wrong'),'binding changed')
    def test_history_admission_guards(self):
        for key in ['full_packet_accepted','baseline_or_experiment_accepted','writes_olean','production_source_changed','production_limits_changed']:
            self.mutated(lambda j,k=key:j['diagnostic'].__setitem__(k,True),'boundary changed')
        self.mutated(lambda j:j['diagnostic']['variants'][1].__setitem__('admitted',True),'admission detected')
    def test_history_outcomes_and_specimens(self):
        self.mutated(lambda j:j['diagnostic']['variants'][1].__setitem__('exit_code',-9),'outcome changed')
        self.mutated(lambda j:j['specimens'].__setitem__(d.previous.NAMES[1],'wrong'),'specimen changed')
        self.mutated(lambda j:j['logs'].__setitem__(d.previous.NAMES[1],'wrong'),'frontier changed')
        self.mutated(lambda j:j['diagnostic']['variants'][0].__setitem__('exact_object_comparison_A_are_extra_diagnostic_inputs',False),'premise classification changed')
    def test_current_mock_fixture(self):
        with tempfile.TemporaryDirectory() as t:
            out=Path(t);old_tests.ObjectTransport().fixture(out)
            self.assertEqual(len(d.validate(self.packet(),out,hosted=False)[0]),2)
    def test_missing_current_fragments(self):
        with tempfile.TemporaryDirectory() as t:
            with self.assertRaises(ValueError):d.validate(self.packet(),Path(t),hosted=False)
    def test_no_admission_or_local_main(self):
        s=Path(d.__file__).read_text()
        for token in ["'writes_olean':False","'production_source_changed':False",'admitted=False,proof_acceptance=False',
            "dir=os.environ['RUNNER_TEMP']","if __name__=='__main__':main()",
            "'maximum_additional_scratch_wall_seconds':2*SECONDS","'total_scheduled_site_scratch_cap_seconds':810"]:
            self.assertIn(token,s)
        self.assertNotIn("'-o'",s)

if __name__=='__main__':unittest.main()

