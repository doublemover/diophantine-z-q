"""Pure synthetic tests. Never invoke Lean/Lake or run hosted observations locally."""
from contextlib import ExitStack
import copy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch, Mock
import diagnose_zero72_prefixes as d
import check_progress_inventory as inv


class GuardTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.folder = self.root/d.PACKET; self.folder.mkdir()
        self.out = self.root/'output'; self.out.mkdir(); (self.out/'lib').mkdir(); (self.out/'logs').mkdir()
        self.passed = ['Passed'+str(i) for i in range(44)]
        order = self.passed+[d.MODULE,'Unselected']
        self.data = {'order':order,'files':{}}
        rows = {}
        for name in order:
            source = 'module\npublic section\n-- mock input only\n'
            p = self.folder/(name+'.lean');p.write_text(source)
            imports = sorted(self.passed+['Base']) if name == d.MODULE else []
            self.data['files'][p.name] = {'sha256':d.ci.sha(p),'imports':imports}
            row = {'source_sha256':d.ci.sha(p),'imports':imports,'status':'not_selected'}
            if name in self.passed:
                row.update(status='compile_pass',exit_code=0,timed_out=False,dependency_artifacts={})
                row['artifacts'] = self.artifacts(self.out/'lib',name)
            elif name == d.MODULE:
                row.update(status='timeout',exit_code=124,timed_out=True)
            if name != 'Unselected':
                log=self.out/'logs'/(name+'.log')
                log.write_text('\nWALL_CLOCK_LIMIT_EXCEEDED\n' if name == d.MODULE else '')
                row['log_sha256']=d.ci.sha(log)
            rows[name]=row
        (self.folder/'intake.json').write_text(json.dumps(self.data))
        (self.folder/'APPLICATION.json').write_text('{}')
        self.intake=d.ci.sha(self.folder/'intake.json')
        self.chosen=d.selection(d.PACKET,self.intake,self.data,[d.MODULE])
        self.cache=self.root/'.cache/progress-ci';self.cache.mkdir(parents=True);(self.cache/'lib').mkdir()
        files=self.artifacts(self.cache/'lib','Base');self.artifacts(self.out/'lib','Base')
        entry={'files':files}
        self.receipt={'schema':d.ci.SCHEMA,'status':'PASS','base':'base','snapshot':'snapshot',
          'scope':'Complete source coverage and recursive axiom audit','audit_result_sha256':'a'*64,'modules':{'Base':entry}}
        (self.cache/'receipt.json').write_text(json.dumps(self.receipt))
        self.project=self.root/'project';self.project.mkdir();(self.project/'Base.lean').write_text('base source')
        self.plan={'snapshot':'snapshot','base':'base','module_order':['Base']}
        audit_log=self.out/'logs/ExperimentAudit.log';audit_log.write_text('EXPERIMENT_AUDIT_PASS declarations=665 modules=44')
        (self.out/'ExperimentAudit.lean').write_text(d.experiment.audit_text(self.passed))
        self.r={'packet':d.PACKET,'packet_sha256':self.intake,'order':order,'modules':rows,'selection':self.chosen,
          'head_sha':'head','run_id':'run','requested_source_commit':'source','requested_source_tree':'tree','request_sha256':'marker',
          'strict_flags':d.FLAGS,'module_seconds':180,'experiment_artifact_reuse':False,'packet_acceptance':False,'new_source_acceptance':False,
          'status':'INVENTORY_RECORDED','baseline_snapshot':'snapshot','baseline_key':'base','verified_baseline_modules':{'Base':entry},
          'checker_sha256':d.ci.sha(Path(inv.__file__)),'production_checker_sha256':d.ci.sha(Path(d.experiment.__file__)),'toolchain':'MOCK','audit':{'status':'audit_pass','exit_code':0,'modules':self.passed,'declarations':665,'log_sha256':d.ci.sha(audit_log)}}
        self.save()
        marker=self.root/d.request_guard.MARKER;marker.parent.mkdir(parents=True);marker.write_text(json.dumps({'request_id':d.REQUEST_ID}))
        event=self.root/'event.json';event.write_text('{}')
        self.stack=ExitStack();self.addCleanup(self.stack.close)
        for obj,name,value in [(d,'BASELINE_NAMES_SHA',d.digest('Base\n')),(d,'APPLICATION_SHA',d.ci.sha(self.folder/'APPLICATION.json')),(d,'INTAKE_SHA',self.intake),(d,'SOURCE_SHA',d.ci.sha(self.folder/(d.MODULE+'.lean'))),
          (d,'SELECTION_SHA',self.chosen['selection_sha256']),(d,'BOUNDED_SHA',d.ci.sha(Path(d.bounded.__file__))),
          (d,'LIMITS_SHA',d.ci.sha(Path(d.bounded.original.__file__))),(d.ci,'ROOT',self.root),(d.ci,'PROJECT',self.project)]:
            self.stack.enter_context(patch.object(obj,name,value))
        mock_source=(self.folder/(d.MODULE+'.lean')).read_text()
        self.stack.enter_context(patch.object(d,'CUTS',{k:(3,d.digest(mock_source+('' if k=='imports' else d.SUFFIX))) for k in d.CUTS}))
        self.stack.enter_context(patch.dict(os.environ,{'GITHUB_ACTIONS':'true','RUNNER_TEMP':str(self.root),'GITHUB_EVENT_PATH':str(event),'GITHUB_SHA':'head','GITHUB_RUN_ID':'run'}))
        self.stack.enter_context(patch.object(d.request_guard,'validate',return_value={'request_id':d.REQUEST_ID,'schema':2,'shards':[{'packet':d.PACKET,'targets':[d.MODULE]}],'job_minutes':210,'execution_commit':'head','source_commit':'source','source_tree':'tree','marker_sha256':'marker'}))
        self.stack.enter_context(patch.object(d.ci,'derive_plan',return_value=self.plan))
        self.stack.enter_context(patch.object(d.ci,'reusable',return_value=True))
        self.stack.enter_context(patch.object(d.time,'time',return_value=0))

    def artifacts(self,lib,name):
        for suffix in d.ci.SUFFIXES:(lib/(name+suffix)).write_text(name+suffix)
        return d.ci.artifact_hashes(lib,name)

    def save(self):
        (self.out/'INVENTORY.json').write_text(json.dumps(self.r))

    def validate(self):return d.validate(self.folder,self.out,self.r,1000)

    def reject(self,change):
        change();self.save()
        with self.assertRaises((ValueError,KeyError,FileNotFoundError)):self.validate()

    def test_valid_exact_fresh_scope(self):
        text,watched,evidence=self.validate()
        self.assertEqual(text['imports'],(self.folder/(d.MODULE+'.lean')).read_text())
        self.assertEqual(evidence['passed_modules'],self.passed)
        self.assertFalse(list((self.out/'logs').glob(d.LABEL)))
        self.assertGreater(len(watched),200)

    def test_wrong_packet(self):self.reject(lambda:self.r.update(packet='other'))
    def test_wrong_selection(self):self.reject(lambda:self.r['selection'].update(selection_sha256='bad'))
    def test_old_run(self):self.reject(lambda:self.r.update(run_id='old'))
    def test_wrong_source(self):self.reject(lambda:self.r.update(requested_source_commit='old'))
    def test_acceptance(self):self.reject(lambda:self.r.update(packet_acceptance=True))
    def test_nonstrict(self):self.reject(lambda:self.r.update(strict_flags=[]))
    def test_incomplete(self):self.reject(lambda:self.r.update(status='INVENTORY_RUNNING'))
    def test_target_pass(self):self.reject(lambda:self.r['modules'][d.MODULE].update(status='compile_pass',exit_code=0))
    def test_wrong_failure(self):self.reject(lambda:self.r['modules'][d.MODULE].update(timed_out=False))
    def test_dependency_fail(self):self.reject(lambda:self.r['modules'][self.passed[0]].update(status='compiler_error'))
    def test_audit_fail(self):self.reject(lambda:self.r['audit'].update(status='audit_failed'))
    def test_audit_wrong_count(self):self.reject(lambda:self.r['audit'].update(declarations=1))
    def test_artifact_corrupt(self):self.reject(lambda:(self.out/'lib'/(self.passed[0]+'.olean')).write_text('bad'))
    def test_baseline_corrupt(self):self.reject(lambda:(self.out/'lib/Base.olean').write_text('bad'))
    def test_failed_artifact_present(self):self.reject(lambda:(self.out/'lib'/(d.MODULE+'.olean')).write_text('bad'))
    def test_source_changed(self):self.reject(lambda:(self.folder/(d.MODULE+'.lean')).write_text('bad'))
    def test_log_changed(self):self.reject(lambda:(self.out/'logs'/(d.MODULE+'.log')).write_text('bad'))
    def test_subset_incomplete(self):self.reject(lambda:self.r['audit'].update(modules=self.passed[:-1]))
    def test_baseline_stale(self):
        with patch.object(d.ci,'reusable',return_value=False):
            with self.assertRaises(ValueError):self.validate()
    def test_no_window(self):
        with self.assertRaises(ValueError):d.validate(self.folder,self.out,self.r,100)
    def test_no_host_no_writes(self):
        with patch.dict(os.environ,{'GITHUB_ACTIONS':'false'}):d.run(self.folder,self.out,{},self.r,1000)
        self.assertFalse((self.out/'logs'/d.LABEL).exists())
    def test_no_eligibility_no_writes(self):
        self.r['packet']='other';d.run(self.folder,self.out,{},self.r,1000)
        self.assertFalse((self.out/'logs'/d.LABEL).exists())
    def test_skip_never_invokes_compiler(self):
        self.r['modules'][d.MODULE]['status']='compile_pass';self.save()
        with patch.object(d.bounded,'bounded_memory') as proc:d.run(self.folder,self.out,{},self.r,1000)
        proc.assert_not_called();record=json.loads((self.out/'logs'/d.LABEL/'DIAGNOSTIC.json').read_text())
        self.assertFalse(record['probe_executed']);self.assertFalse(record['proof_acceptance'])
    def test_mock_probe_preserves_inventory_and_artifacts(self):
        before=(self.out/'INVENTORY.json').read_bytes()
        def compiler(source,root,env,log):
            log.write_text('MOCK DIAGNOSTIC ONLY')
            return {'exit_code':1,'limit':None,'admitted':False}
        with patch.object(d.ci,'environment',return_value=({'LEAN_PATH':'mock'},'MOCK')),patch.object(d.bounded,'bounded_memory',side_effect=compiler):
            d.run(self.folder,self.out,{'LEAN_PATH':'mock'},self.r,1000)
        record=json.loads((self.out/'logs'/d.LABEL/'DIAGNOSTIC.json').read_text());self.assertEqual(record['status'],'RECORDED')
        self.assertEqual(before,(self.out/'INVENTORY.json').read_bytes());self.assertFalse(record['proof_acceptance'])
    def test_environment_recheck_uses_exact_project_cwd(self):
        before=Path.cwd()
        def environment(project,lib):
            self.assertEqual(Path.cwd(),self.project)
            self.assertEqual(project,self.project)
            self.assertEqual(lib,self.out/'lib')
            return {'LEAN_PATH':'mock'},'MOCK'
        def compiler(source,root,env,log):
            self.assertEqual(Path.cwd(),before)
            log.write_text('MOCK');return {'exit_code':1,'limit':None}
        with patch.object(d.ci,'environment',side_effect=environment),patch.object(d.bounded,'bounded_memory',side_effect=compiler):
            d.run(self.folder,self.out,{'LEAN_PATH':'mock'},self.r,1000)
        self.assertEqual(Path.cwd(),before)
        self.assertEqual(json.loads((self.out/'logs'/d.LABEL/'DIAGNOSTIC.json').read_text())['status'],'RECORDED')

    def test_environment_failure_restores_cwd_and_skips(self):
        before=Path.cwd()
        def environment(project,lib):
            self.assertEqual(Path.cwd(),self.project)
            raise ValueError('MOCK wrong compiler pin')
        with patch.object(d.ci,'environment',side_effect=environment),patch.object(d.bounded,'bounded_memory') as compiler:
            d.run(self.folder,self.out,{'LEAN_PATH':'mock'},self.r,1000)
        self.assertEqual(Path.cwd(),before);compiler.assert_not_called()
        record=json.loads((self.out/'logs'/d.LABEL/'DIAGNOSTIC.json').read_text())
        self.assertEqual(record['status'],'SKIPPED_OR_INVALID');self.assertFalse(record['probe_executed'])

    def test_mock_mutation_invalidates(self):
        def compiler(source,root,env,log):
            log.write_text('MOCK');(self.out/'INVENTORY.json').write_text('{}');return {'exit_code':0}
        with patch.object(d.ci,'environment',return_value=({'LEAN_PATH':'mock'},'MOCK')),patch.object(d.bounded,'bounded_memory',side_effect=compiler):
            d.run(self.folder,self.out,{'LEAN_PATH':'mock'},self.r,1000)
        self.assertEqual(json.loads((self.out/'logs'/d.LABEL/'DIAGNOSTIC.json').read_text())['status'],'SKIPPED_OR_INVALID')


    def test_wrong_marker_and_extra_shard(self):
        valid=d.request_guard.validate.return_value
        for extra in ({'request_id':'ordinary'},{'job_minutes':220},{'shards':valid['shards']*2}):
            with patch.object(d.request_guard,'validate',return_value=valid|extra),self.assertRaises(ValueError):
                self.validate()

    def test_application_changed(self):self.reject(lambda:(self.folder/'APPLICATION.json').write_text('different'))

    def test_different_timeout_text_even_with_fresh_digest(self):
        log=self.out/'logs'/(d.MODULE+'.log');log.write_text('some diagnostic')
        self.reject(lambda:self.r['modules'][d.MODULE].update(log_sha256=d.ci.sha(log)))

    def test_binding_detects_wrong_prefix(self):
        with patch.object(d,'CUTS',{'imports':(1,'0'*64)}),self.assertRaises(ValueError):
            d.specimens((self.folder/(d.MODULE+'.lean')).read_text())

    def test_max_five_unique_exact_inputs(self):
        def compiler(path,root,env,log):
            self.assertEqual(path.name,d.MODULE+'.lean')
            self.assertEqual(path.parent,root)
            self.assertEqual(list(root.iterdir()),[path])
            log.write_text('MOCK strict exit');return {'exit_code':0,'limit':None}
        with patch.object(d.ci,'environment',return_value=({'LEAN_PATH':'mock'},'MOCK')),patch.object(d.bounded,'bounded_memory',side_effect=compiler) as c:
            d.run(self.folder,self.out,{'LEAN_PATH':'mock'},self.r,1000)
        rec=json.loads((self.out/'logs'/d.LABEL/'DIAGNOSTIC.json').read_text())
        self.assertEqual([r['prefix'] for r in rec['results']],['imports','all_helpers','source_normalized','regroup_root','source_coordinate_original'])
        self.assertEqual(c.call_count,5);self.assertFalse(rec['proof_acceptance'])
        for r in rec['results']:
            self.assertEqual(r['input_sha256'],d.CUTS[r['prefix']][1])

    def test_adaptive_and_stop(self):
        def next_key(key,exit_code,limit):
            return d.choose([{'prefix':key,'exit_code':exit_code,'limit':limit}])
        self.assertEqual(next_key('all_helpers',-9,'SCRATCH_WALL_LIMIT'),'three_helpers')
        self.assertEqual(next_key('source_normalized',-9,'SCRATCH_WALL_LIMIT'),'chart_setup')
        for key in ['imports','chart_setup','three_helpers','regroup_root','source_coordinate_original']:
            self.assertIsNone(next_key(key,-9,'SCRATCH_WALL_LIMIT'))
        for key in d.CUTS:
            self.assertIsNone(next_key(key,1,None))
            self.assertIsNone(next_key(key,-9,'SCRATCH_LOG_LIMIT'))

    def test_new_dispatch_does_not_replace_contact(self):
        self.r['selection']['selection_sha256']='d291531b2c808956614c3b020f6289f11c693022c81957ab611672d35ca74821'
        with patch.object(inv,'observe_contact') as contact,patch.object(d,'run') as cb:
            inv.observe_diagnostics(self.folder,self.out,{},self.r,1000)
            cb.assert_called_once();contact.assert_not_called()
            self.r['packet']='other';inv.observe_diagnostics(self.folder,self.out,{},self.r,1000)
            self.assertEqual(cb.call_count,1);contact.assert_called_once()

    def test_no_opt_in_no_output(self):
        (self.root/d.request_guard.MARKER).write_text('{}')
        with patch.object(d.bounded,'bounded_memory') as compiler:
            d.run(self.folder,self.out,{},self.r,1000)
        compiler.assert_not_called();self.assertFalse((self.out/'logs'/d.LABEL).exists())

    def test_inexact_packet_baseline_set(self):
        with patch.object(d,'BASELINE_NAMES_SHA','0'*64),self.assertRaises(ValueError):
            self.validate()


class FrozenPrefixTests(unittest.TestCase):
    def test_frozen_source_and_every_endpoint(self):
        packet = Path(__file__).resolve().parents[1]/'quartics/quartic-318-326/proof/experiments'/d.PACKET
        original=(packet/(d.MODULE+'.lean')).read_text()
        self.assertEqual(d.ci.sha(packet/'APPLICATION.json'),d.APPLICATION_SHA)
        self.assertEqual(d.ci.sha(packet/'intake.json'),d.INTAKE_SHA)
        texts=d.specimens(original)
        next_lines={'imports':'#eval','three_helpers':'/-- The root-generator',
                    'all_helpers':'variable (b:Fin','chart_setup':'#eval','source_normalized':'#eval',
                    'regroup_root':'#eval','source_coordinate_original':'#eval'}
        for key,(count,_) in d.CUTS.items():
            prefix=''.join(original.splitlines(keepends=True)[:count])
            self.assertEqual(texts[key],prefix+('' if key=='imports' else d.SUFFIX))
            self.assertTrue(original.splitlines()[count].startswith(next_lines[key]))
        self.assertEqual(set(next_lines),set(d.CUTS))

if __name__=='__main__':
    unittest.main()
