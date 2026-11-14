#!/usr/bin/env python3
"""Static source/guard tests only. Never execute Lean or the runner."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import diagnose_geometry_frontiers as d

class GeometryTests(unittest.TestCase):
    def folder(self, packet):
        return d.ci.ROOT/'quartics/quartic-318-326/proof/experiments'/packet
    def test_cases_and_limits(self):
        for packet,cfg in d.CONFIG.items():
            src=(self.folder(packet)/(cfg['module']+'.lean')).read_text()
            cases=d.variants(packet,src)
            self.assertEqual(len(cases),6)
            opts=[x for x in src.splitlines() if x.startswith('set_option ')]
            for text in cases.values():
                self.assertNotIn('sorry',text);self.assertNotIn('axiom ',text)
                self.assertNotIn('set_option maxRecDepth',text)
                self.assertEqual([x for x in text.splitlines() if x.startswith('set_option ') and not x.startswith(('set_option diagnostics','set_option profiler','set_option stderrAsMessages'))],opts)
                self.assertIn('GEOMETRY_DIAGNOSTIC',text)
                self.assertIn('set_option stderrAsMessages false',text)
                self.assertIn('run_cmd do\n  let e ← IO.getStderr\n  e.putStrLn',text)
                self.assertIn('\n  e.flush\n',text)
                self.assertTrue(text.endswith('\nend '+cfg['module']+'\n'))
                self.assertNotIn('theorem common_finite',text)
                self.assertNotIn('theorem finite_square :',text)
    def test_exact_prefix_and_final_declaration(self):
        for packet,cfg in d.CONFIG.items():
            src=(self.folder(packet)/(cfg['module']+'.lean')).read_text();cases=d.variants(packet,src)
            prefix=cases['exact_prefix'].split('\nset_option diagnostics true')[0]
            self.assertTrue(src.startswith(prefix))
            final='exact_infinity_inverse_square' if 'center' in packet else 'exact_commonRestriction'
            body=cases[final].split('GEOMETRY_DIAGNOSTIC '+final+'"\n  e.flush\n',1)[1].rsplit('\nend ',1)[0].rstrip()
            self.assertIn(body,src)
    def test_actual_maps_and_witnesses_retained(self):
        for packet,cfg in d.CONFIG.items():
            cases=d.variants(packet,(self.folder(packet)/(cfg['module']+'.lean')).read_text())
            if 'center' in packet:
                for name in ['typed_ring_square','typed_helper','typed_square_final_wrappers','exact_infinity_inverse_square']:
                    self.assertIn('exact IntegralRationalInfinityMap318.infinity_restriction c a',cases[name])
                self.assertIn('have h := spec_inverse_square',cases['typed_helper'])
                for carrier in ['IntegralInfinityChart318.Order ℚ c','IntegralOverlapChartMaps318.Overlap ℚ c','InfinityOpenChart318.OpenOrder c','ContactKummerOrder318.OpenOrder c']:
                    self.assertIn('CommRingCat.of ('+carrier+')',cases['typed_ring_inputs'])
            else:
                self.assertIn('(finiteRestriction R c) (oldY R c) (finiteRestriction_X R c)',cases['complete_unit_wrapper'])
                self.assertNotIn('(finiteRestriction_X R c)\n',cases['partial_unit_wrapper'])
    def test_mutated_source_rejected(self):
        for packet,cfg in d.CONFIG.items():
            src=(self.folder(packet)/(cfg['module']+'.lean')).read_text()
            with self.assertRaisesRegex(ValueError,'Frozen source'):d.variants(packet,src+'\n')
    def test_hosted_guard(self):
        with patch.dict(d.os.environ,{},clear=True):
            with self.assertRaisesRegex(ValueError,'Hosted Actions only'):d.validate(Path('/nonexistent'),Path('/nonexistent'))
    def test_full_result_required(self):
        for packet in d.CONFIG:
            with tempfile.TemporaryDirectory() as t:
                with self.assertRaisesRegex(ValueError,'Mandatory full'):d.validate(self.folder(packet),Path(t),hosted=False)
    def fixture(self,packet,out):
        cfg=d.CONFIG[packet];data=json.loads((self.folder(packet)/'intake.json').read_text())
        order=data['order'][:data['order'].index(cfg['module'])+1]
        return {'packet':packet,'packet_sha256':cfg['intake'],'commands':[{'module':n,'exit_code':int(n==cfg['module'])} for n in order]}
    def test_wrong_result_and_frontier_rejected(self):
        for packet in d.CONFIG:
            with tempfile.TemporaryDirectory() as t:
                out=Path(t);p=out/'RESULT.json';p.write_text('{}')
                with self.assertRaisesRegex(ValueError,'Wrong full'):d.validate(self.folder(packet),out,hosted=False)
                r=self.fixture(packet,out);r['commands']=r['commands'][:-1];p.write_text(json.dumps(r))
                with self.assertRaisesRegex(ValueError,'exactly the observed'):d.validate(self.folder(packet),out,hosted=False)
                r=self.fixture(packet,out);r['commands'][-1]['exit_code']=0;p.write_text(json.dumps(r))
                with self.assertRaisesRegex(ValueError,'outcomes changed'):d.validate(self.folder(packet),out,hosted=False)
    def test_dependency_and_caps_guards(self):
        for packet,cfg in d.CONFIG.items():
            with tempfile.TemporaryDirectory() as t:
                out=Path(t);(out/'RESULT.json').write_text(json.dumps(self.fixture(packet,out)))
                with self.assertRaisesRegex(ValueError,'dependency missing'):d.validate(self.folder(packet),out,hosted=False)
                (out/'lib').mkdir()
                for name in cfg['imports']:(out/'lib'/(name+'.olean')).write_text('static fixture, never loaded by Lean')
                self.assertEqual(len(d.validate(self.folder(packet),out,hosted=False)[0]),6)
                with patch.object(d.runner.original,'SECONDS',91):
                    with self.assertRaisesRegex(ValueError,'caps changed'):d.validate(self.folder(packet),out,hosted=False)
    def test_no_acceptance_or_olean(self):
        self.assertEqual(d.SECONDS,90);self.assertEqual(d.MAX_BYTES,2*1024*1024)
        text=Path(d.__file__).read_text();self.assertNotIn("'-o'",text)
        self.assertIn("'full_packet_accepted': False",text)
        self.assertIn("'production_source_changed': False",text)
if __name__=='__main__':unittest.main()
