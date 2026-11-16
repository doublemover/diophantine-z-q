"""Pure synthetic tests. Never invoke Lean/Lake or run hosted observations locally."""
from contextlib import ExitStack
import copy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch, Mock
import diagnose_contact_refinement as d
import check_progress_inventory as inv
import test_progress_inventory as inventory_tests


class GuardTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.folder = self.root/d.PACKET; self.folder.mkdir()
        self.out = self.root/'output'; self.out.mkdir(); (self.out/'lib').mkdir(); (self.out/'logs').mkdir()
        self.passed = ['Passed'+str(i) for i in range(43)]
        order = self.passed+[d.MODULE,'Unselected']
        self.data = {'order':order,'files':{}}
        rows = {}
        for name in order:
            source = 'module\npublic section\nset_option maxHeartbeats 650000\n'
            p = self.folder/(name+'.lean');p.write_text(source)
            imports = sorted(self.passed+['Base']) if name == d.MODULE else []
            self.data['files'][p.name] = {'sha256':d.ci.sha(p),'imports':imports}
            row = {'source_sha256':d.ci.sha(p),'imports':imports,'status':'not_selected'}
            if name in self.passed:
                row.update(status='compile_pass',exit_code=0,timed_out=False,dependency_artifacts={})
                row['artifacts'] = self.artifacts(self.out/'lib',name)
            elif name == d.MODULE:
                row.update(status='compiler_error',exit_code=1,timed_out=False)
            if name != 'Unselected':
                log=self.out/'logs'/(name+'.log')
                log.write_text('(deterministic) timeout at `whnf`, maximum number of heartbeats (650000)' if name == d.MODULE else '')
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
        audit_log=self.out/'logs/ExperimentAudit.log';audit_log.write_text('EXPERIMENT_AUDIT_PASS declarations=573 modules=43')
        (self.out/'ExperimentAudit.lean').write_text(d.experiment.audit_text(self.passed))
        self.r={'packet':d.PACKET,'packet_sha256':self.intake,'order':order,'modules':rows,'selection':self.chosen,
          'head_sha':'head','run_id':'run','requested_source_commit':'source','requested_source_tree':'tree','request_sha256':'marker',
          'strict_flags':d.FLAGS,'module_seconds':180,'experiment_artifact_reuse':False,'packet_acceptance':False,'new_source_acceptance':False,
          'status':'INVENTORY_RECORDED','baseline_snapshot':'snapshot','baseline_key':'base','verified_baseline_modules':{'Base':entry},
          'checker_sha256':d.ci.sha(Path(inv.__file__)),'production_checker_sha256':d.ci.sha(Path(d.experiment.__file__)),'toolchain':'MOCK','audit':{'status':'audit_pass','exit_code':0,'modules':self.passed,'declarations':573,'log_sha256':d.ci.sha(audit_log)}}
        self.save()
        event=self.root/'event.json';event.write_text('{}')
        self.stack=ExitStack();self.addCleanup(self.stack.close)
        for obj,name,value in [(d,'INTAKE_SHA',self.intake),(d,'SOURCE_SHA',d.ci.sha(self.folder/(d.MODULE+'.lean'))),
          (d,'SELECTION_SHA',self.chosen['selection_sha256']),(d,'BOUNDED_SHA',d.ci.sha(Path(d.bounded.__file__))),
          (d,'LIMITS_SHA',d.ci.sha(Path(d.bounded.original.__file__))),(d.ci,'ROOT',self.root),(d.ci,'PROJECT',self.project)]:
            self.stack.enter_context(patch.object(obj,name,value))
        self.stack.enter_context(patch.dict(os.environ,{'GITHUB_ACTIONS':'true','RUNNER_TEMP':str(self.root),'GITHUB_EVENT_PATH':str(event),'GITHUB_SHA':'head','GITHUB_RUN_ID':'run'}))
        self.stack.enter_context(patch.object(d.request_guard,'validate',return_value={'execution_commit':'head','source_commit':'source','source_tree':'tree','marker_sha256':'marker'}))
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
        self.assertEqual(text.replace(d.OPTIONS,'',1),(self.folder/(d.MODULE+'.lean')).read_text())
        self.assertEqual(evidence['passed_modules'],self.passed)
        self.assertFalse(list(self.out.glob(d.LABEL)))
        self.assertGreater(len(watched),200)

    def test_wrong_packet(self):self.reject(lambda:self.r.update(packet='other'))
    def test_wrong_selection(self):self.reject(lambda:self.r['selection'].update(selection_sha256='bad'))
    def test_old_run(self):self.reject(lambda:self.r.update(run_id='old'))
    def test_wrong_source(self):self.reject(lambda:self.r.update(requested_source_commit='old'))
    def test_acceptance(self):self.reject(lambda:self.r.update(packet_acceptance=True))
    def test_nonstrict(self):self.reject(lambda:self.r.update(strict_flags=[]))
    def test_incomplete(self):self.reject(lambda:self.r.update(status='INVENTORY_RUNNING'))
    def test_target_pass(self):self.reject(lambda:self.r['modules'][d.MODULE].update(status='compile_pass',exit_code=0))
    def test_wrong_failure(self):self.reject(lambda:self.r['modules'][d.MODULE].update(timed_out=True))
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
        self.assertFalse((self.out/d.LABEL).exists())
    def test_no_eligibility_no_writes(self):
        self.r['packet']='other';d.run(self.folder,self.out,{},self.r,1000)
        self.assertFalse((self.out/d.LABEL).exists())
    def test_skip_never_invokes_compiler(self):
        self.r['modules'][d.MODULE]['status']='compile_pass';self.save()
        with patch.object(d.bounded,'bounded_memory') as proc:d.run(self.folder,self.out,{},self.r,1000)
        proc.assert_not_called();record=json.loads((self.out/d.LABEL/'DIAGNOSTIC.json').read_text())
        self.assertFalse(record['probe_executed']);self.assertFalse(record['proof_acceptance'])
    def test_mock_probe_preserves_inventory_and_artifacts(self):
        before=(self.out/'INVENTORY.json').read_bytes()
        def compiler(source,root,env,log):
            log.write_text('MOCK DIAGNOSTIC ONLY')
            return {'exit_code':1,'limit':None,'admitted':False}
        with patch.object(d.ci,'environment',return_value=({'LEAN_PATH':'mock'},'MOCK')),patch.object(d.bounded,'bounded_memory',side_effect=compiler):
            d.run(self.folder,self.out,{'LEAN_PATH':'mock'},self.r,1000)
        record=json.loads((self.out/d.LABEL/'DIAGNOSTIC.json').read_text());self.assertEqual(record['status'],'RECORDED')
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
        self.assertEqual(json.loads((self.out/d.LABEL/'DIAGNOSTIC.json').read_text())['status'],'RECORDED')

    def test_environment_failure_restores_cwd_and_skips(self):
        before=Path.cwd()
        def environment(project,lib):
            self.assertEqual(Path.cwd(),self.project)
            raise ValueError('MOCK wrong compiler pin')
        with patch.object(d.ci,'environment',side_effect=environment),patch.object(d.bounded,'bounded_memory') as compiler:
            d.run(self.folder,self.out,{'LEAN_PATH':'mock'},self.r,1000)
        self.assertEqual(Path.cwd(),before);compiler.assert_not_called()
        record=json.loads((self.out/d.LABEL/'DIAGNOSTIC.json').read_text())
        self.assertEqual(record['status'],'SKIPPED_OR_INVALID');self.assertFalse(record['probe_executed'])

    def test_mock_mutation_invalidates(self):
        def compiler(source,root,env,log):
            log.write_text('MOCK');(self.out/'INVENTORY.json').write_text('{}');return {'exit_code':0}
        with patch.object(d.ci,'environment',return_value=({'LEAN_PATH':'mock'},'MOCK')),patch.object(d.bounded,'bounded_memory',side_effect=compiler):
            d.run(self.folder,self.out,{'LEAN_PATH':'mock'},self.r,1000)
        self.assertEqual(json.loads((self.out/d.LABEL/'DIAGNOSTIC.json').read_text())['status'],'SKIPPED_OR_INVALID')


class CallbackTests(unittest.TestCase):
    def test_callback_before_cleanup_and_failure_does_not_change_status(self):
        with tempfile.TemporaryDirectory() as tmp:
            helper=inventory_tests.InventoryTests();f,data,out,lib,r=helper.fixture(Path(tmp),{'A':[],'B':['A']})
            compile_fn,calls=helper.compiler({'B':1});seen=[]
            def callback(*args):
                self.assertTrue((lib/'A.olean').is_file());self.assertFalse((lib/'B.olean').exists())
                self.assertEqual(r['audit']['status'],'audit_pass');self.assertEqual(r['status'],'INVENTORY_RECORDED')
                self.assertEqual(json.loads((out/'INVENTORY.json').read_text()),r);seen.append(True)
                raise RuntimeError('MOCK OBSERVER FAILURE')
            inv.inventory(f,data,out,lib,{},r,1000,compile_fn,lambda:0,callback)
            self.assertEqual(seen,[True]);self.assertFalse(list(lib.iterdir()))
            self.assertEqual(r['status'],'INVENTORY_RECORDED');self.assertEqual(r['modules']['B']['status'],'compiler_error')
            self.assertFalse(r['packet_acceptance']);self.assertFalse((out/'quarantine').exists())
    def test_inventory_checkout_preserves_parent_for_guard(self):
        root=Path(__file__).resolve().parents[1]
        workflow=(root/'.github/workflows/progress-inventory.yml').read_text()
        inventory=workflow.split('  inventory:',1)[1]
        checkout=inventory.split('      - id: checkout',1)[1].split('      - id: python',1)[0]
        self.assertIn('          fetch-depth: 2\n',checkout)
        self.assertIn('          sparse-checkout: |',checkout)

    def test_noncontact_hook_does_not_import_diagnostic(self):
        with patch('builtins.__import__',side_effect=AssertionError('should not import')):
            inv.observe_contact(None,None,None,{'packet':'other'},0)


if __name__=='__main__':
    unittest.main()
