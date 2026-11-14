#!/usr/bin/env python3
"""Static generation/guard tests only; never run Lean or the diagnostic runner."""
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch
import diagnose_picard_reconstructed_overlap as d

class PicardDiagnostics(unittest.TestCase):
    def packet(self):
        return d.ci.ROOT/'quartics/quartic-318-326/proof/experiments'/d.PACKET
    def source(self):
        return (self.packet()/(d.MODULE+'.lean')).read_text()
    def fixture(self, out):
        data=json.loads((self.packet()/'intake.json').read_text())
        order=data['order'][:data['order'].index(d.MODULE)+1]
        result={'packet':d.PACKET,'packet_sha256':d.INTAKE_SHA,'commands':[
            {'module':n,'exit_code':124 if n==d.MODULE else 0} for n in order]}
        (out/'RESULT.json').write_text(json.dumps(result))
        (out/'logs').mkdir();(out/'lib').mkdir()
        text='\n'.join(d.REQUIRED_MARKERS[:2]+['PICARD_SITE_PROFILER_CONTROL took 0.00511ms']+d.REQUIRED_MARKERS[2:])+'\nWALL_CLOCK_LIMIT_EXCEEDED\n'
        (out/'logs'/(d.MODULE+'.log')).write_text(text)
        (out/'lib'/(d.DEPENDENCY+'.olean')).write_text('FAKE static fixture, never imported by Lean')
        return result
    def test_exact_three_variants(self):
        cases=d.variants(self.source())
        self.assertEqual(set(cases),{'exact_prefix_control','exact_statement_placeholder','exact_unchanged_helper'})
        for name,text in cases.items():
            self.assertEqual(text.count('sorry'),int(name=='exact_statement_placeholder'))
            self.assertNotIn('axiom ',text);self.assertNotIn(d.FORBIDDEN_MARKER,text)
            self.assertIn('PICARD_NONADMITTED_'+name+'_COMMAND_END',text)
            self.assertTrue(text.endswith(d.END))
    def test_exact_prefix_and_statement_and_proof(self):
        source=self.source();prefix,decl,statement=d.segments(source);cases=d.variants(source)
        self.assertTrue(source.startswith(prefix));self.assertIn(decl,source)
        self.assertIn(prefix+decl,cases['exact_unchanged_helper'])
        self.assertIn(prefix+statement+' := by\n  sorry\n',cases['exact_statement_placeholder'])
        self.assertNotIn('private lemma reconstructed_actual_overlap',cases['exact_prefix_control'])
        self.assertNotIn('BODY_00',cases['exact_statement_placeholder'])
        self.assertNotIn('lemma original_overlap :', ''.join(cases.values()))
    def test_original_limits_and_control(self):
        original=[x for x in self.source().splitlines() if x.startswith('set_option ') and 'profiler' not in x]
        for text in d.variants(self.source()).values():
            self.assertEqual([x for x in text.splitlines() if x.startswith('set_option ') and 'profiler' not in x],original)
            self.assertIn('PICARD_SITE_PROFILER_CONTROL_BEGIN',text)
            self.assertIn('PICARD_SITE_PROFILER_CONTROL_END',text)
            self.assertIn('.set `profiler.threshold (0 : Nat)',text)
            self.assertIn('out.flush',text)
        self.assertEqual(d.SECONDS,90);self.assertEqual(d.MAX_BYTES,2*1024*1024)
    def test_mutated_source_rejected(self):
        with self.assertRaisesRegex(ValueError,'Frozen source'):d.variants(self.source()+'\n')
    def test_hosted_guard(self):
        with patch.dict(d.os.environ,{},clear=True):
            with self.assertRaisesRegex(ValueError,'Hosted Actions only'):
                d.validate(Path('/not-used'),Path('/not-used'))
    def test_missing_result(self):
        with tempfile.TemporaryDirectory() as t:
            with self.assertRaisesRegex(ValueError,'Mandatory full'):
                d.validate(self.packet(),Path(t),hosted=False)
    def test_correct_static_fixture(self):
        with tempfile.TemporaryDirectory() as t:
            out=Path(t);self.fixture(out);self.assertEqual(len(d.validate(self.packet(),out,hosted=False)[0]),3)
    def test_result_and_frontier_guards(self):
        with tempfile.TemporaryDirectory() as t:
            out=Path(t);result=self.fixture(out);path=out/'RESULT.json'
            bad=dict(result);bad['packet_sha256']='wrong';path.write_text(json.dumps(bad))
            with self.assertRaisesRegex(ValueError,'Wrong full'):d.validate(self.packet(),out,hosted=False)
            bad=dict(result);bad['commands']=result['commands'][:-1];path.write_text(json.dumps(bad))
            with self.assertRaisesRegex(ValueError,'exactly the observed'):d.validate(self.packet(),out,hosted=False)
            for code in [0,1]:
                result['commands'][-1]['exit_code']=code;path.write_text(json.dumps(result))
                with self.assertRaisesRegex(ValueError,'outcomes changed'):d.validate(self.packet(),out,hosted=False)
    def test_log_marker_guards(self):
        with tempfile.TemporaryDirectory() as t:
            out=Path(t);self.fixture(out);p=out/'logs'/(d.MODULE+'.log');text=p.read_text()
            for marker in d.REQUIRED_MARKERS:
                p.write_text(text.replace(marker,''))
                with self.assertRaisesRegex(ValueError,'marker boundary'):d.validate(self.packet(),out,hosted=False)
            p.write_text('\n'.join(reversed(d.REQUIRED_MARKERS)))
            with self.assertRaisesRegex(ValueError,'marker order'):d.validate(self.packet(),out,hosted=False)
            p.write_text(text+d.FORBIDDEN_MARKER)
            with self.assertRaisesRegex(ValueError,'marker boundary'):d.validate(self.packet(),out,hosted=False)
            p.write_text(text.replace('PICARD_SITE_PROFILER_CONTROL took','removed timing'))
            with self.assertRaisesRegex(ValueError,'positive control missing'):d.validate(self.packet(),out,hosted=False)
            p.write_text(text.replace('WALL_CLOCK_LIMIT_EXCEEDED',''))
            with self.assertRaisesRegex(ValueError,'wall-limit'):d.validate(self.packet(),out,hosted=False)
    def test_dependency_caps_and_target_guards(self):
        with tempfile.TemporaryDirectory() as t:
            out=Path(t);self.fixture(out);dep=out/'lib'/(d.DEPENDENCY+'.olean');dep.unlink()
            with self.assertRaisesRegex(ValueError,'dependency missing'):d.validate(self.packet(),out,hosted=False)
            dep.write_text('static only')
            for suffix in d.ci.SUFFIXES:
                target=out/'lib'/(d.MODULE+suffix);target.write_text('static only')
                with self.assertRaisesRegex(ValueError,'importable artifact'):d.validate(self.packet(),out,hosted=False)
                target.unlink()
            with patch.object(d.runner.original,'SECONDS',91):
                with self.assertRaisesRegex(ValueError,'caps changed'):d.validate(self.packet(),out,hosted=False)
            with patch.object(d.runner.original,'MAX_BYTES',2*1024*1024+1):
                with self.assertRaisesRegex(ValueError,'caps changed'):d.validate(self.packet(),out,hosted=False)
            with patch.object(d.ci,'FLAGS',['-Ddebug.skipKernelTC=true']):
                with self.assertRaisesRegex(ValueError,'flags changed'):d.validate(self.packet(),out,hosted=False)
    def test_metadata_and_source_binding_guards(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);p=root/d.PACKET;p.mkdir();out=root/'output';out.mkdir();self.fixture(out)
            for name in ['intake.json','APPLICATION.json']:
                shutil.copy2(self.packet()/name,p/name)
            for src in self.packet().glob('*.lean'):shutil.copy2(src,p/src.name)
            for name,expected in [('intake.json','Frozen intake'),('APPLICATION.json','Frozen application')]:
                original=(p/name).read_bytes();(p/name).write_bytes(original+b'\n')
                with self.assertRaisesRegex(ValueError,expected):d.validate(p,out,hosted=False)
                (p/name).write_bytes(original)
            src=p/(d.MODULE+'.lean');src.write_text(src.read_text()+'\n')
            with self.assertRaisesRegex(ValueError,'Source binding changed'):d.validate(p,out,hosted=False)
    def test_no_admission_or_compiler_output(self):
        text=Path(d.__file__).read_text()
        self.assertNotIn("'-o'",text);self.assertIn("'writes_olean': False",text)
        self.assertIn("'production_source_changed': False",text)
        self.assertIn('proof_acceptance=False',text);self.assertIn('Hosted Actions only',text)
        self.assertIn("dir=os.environ['RUNNER_TEMP']",text)

if __name__=='__main__':unittest.main()
