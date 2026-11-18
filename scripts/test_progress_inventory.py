"""Synthetic scheduling and trust controls. Never invoke Lean or Lake."""
from contextlib import ExitStack
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch
import check_progress_inventory as inv
import check_progress_experiment as exp
import check_progress_lean as ci


class InventoryTests(unittest.TestCase):
    def fixture(self, root, graph):
        folder = root / 'packet'; folder.mkdir()
        output = root / 'output'; output.mkdir()
        lib = output / 'lib'; lib.mkdir()
        data = {'order': list(graph), 'files': {}}
        rows = {}
        for name, deps in graph.items():
            source = 'module\n' + ''.join('import '+d+'\n' for d in deps)
            (folder / (name+'.lean')).write_text(source)
            data['files'][name+'.lean'] = {'sha256': hashlib.sha256(source.encode()).hexdigest(), 'imports': deps}
            rows[name] = {'status': 'pending', 'source_sha256': data['files'][name+'.lean']['sha256'],
                          'imports': deps, 'occurrence': 'packet/'+name}
        (folder/'intake.json').write_text(json.dumps(data))
        result = {'status': 'INVENTORY_RUNNING', 'packet_acceptance': False,
                  'modules': rows, 'audit': {'status': 'not_run'}}
        return folder, data, output, lib, result

    def compiler(self, codes=None, audit_code=0, hooks=None):
        calls = []
        def compile_fn(source, target, root, env, logs):
            name = source.stem;calls.append(name);logs.mkdir(exist_ok=True)
            code = (codes or {}).get(name, 0) if target else audit_code
            if hooks: hooks(name, target)
            if target:
                target.parent.mkdir(parents=True, exist_ok=True)
                for suffix in ci.SUFFIXES:
                    target.with_suffix(suffix).write_text('synthetic '+name+suffix)
                text = 'synthetic result\n'
            else:
                count = source.read_text().count('import all ')
                text = f'EXPERIMENT_AUDIT_PASS declarations=12 modules={count}\n'
            (logs/(name+'.log')).write_text(text)
            return {'exit_code': code, 'timed_out': code == 124, 'seconds': 0,
                    'log_sha256': ci.sha(logs/(name+'.log')), 'command': ['MOCK', name]}
        return compile_fn, calls

    def sweep(self, root, graph, codes=None, audit_code=0, deadline=1000, clock=lambda:0, hooks=None):
        folder,data,out,lib,result=self.fixture(root,graph)
        compiler,calls=self.compiler(codes,audit_code,hooks)
        inv.inventory(folder,data,out,lib,{},result,deadline,compiler,clock)
        return result,calls,out,lib

    def test_failure_does_not_hide_independent_branch(self):
        with tempfile.TemporaryDirectory() as t:
            r,c,o,l=self.sweep(Path(t),{'A':[], 'B':['A'], 'C':[]},{'A':1})
            self.assertEqual(c,['A','C','ExperimentAudit'])
            self.assertEqual(r['modules']['B']['status'],'blocked_by_import')
            self.assertEqual(r['modules']['B']['root_causes'],['A'])
            self.assertEqual(r['audit']['modules'],['C']);self.assertEqual(r['audit']['status'],'audit_pass')
            self.assertTrue(r['dependency_ready_inventory_complete']);self.assertFalse(r['all_packet_modules_compiled'])
            self.assertFalse(r['packet_acceptance']);self.assertFalse(list(l.glob('*')))

    def test_diamond_and_transitive_causes(self):
        with tempfile.TemporaryDirectory() as t:
            r,c,_,_=self.sweep(Path(t),{'A':[],'B':[],'C':['A','B'],'D':['C']},{'A':1,'B':124})
            self.assertEqual(r['modules']['D']['root_causes'],['A','B'])
            self.assertEqual(r['modules']['D']['blocker_statuses'],{'A':'compiler_error','B':'timeout'})
            self.assertEqual(c,['A','B']);self.assertEqual(r['audit']['status'],'not_run_empty')

    def test_failed_split_artifacts_cannot_supply_imports(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t)
            def hook(name,target):
                if name=='C':
                    self.assertFalse(any((root/'output/lib'/('A'+s)).exists() for s in ci.SUFFIXES))
                    self.assertFalse((root/'output/quarantine/A').exists())
            r,c,_,_=self.sweep(root,{'A':[],'B':['A'],'C':[]},{'A':124},hooks=hook)
            self.assertNotIn('B',c)

    def test_success_artifacts_used_only_in_same_sweep(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t)
            def hook(name,target):
                if name=='B':self.assertTrue((root/'output/lib/A.olean').is_file())
            r,c,_,lib=self.sweep(root,{'A':[],'B':['A']},hooks=hook)
            self.assertEqual(r['modules']['B']['dependency_artifacts'],{'A':r['modules']['A']['artifacts']})
            self.assertFalse(list(lib.iterdir()));self.assertEqual(c,['A','B','ExperimentAudit'])

    def test_budget_explicit_and_downstream_not_compiler_failure(self):
        with tempfile.TemporaryDirectory() as t:
            r,c,_,_=self.sweep(Path(t),{'A':[],'B':['A'],'C':[]},deadline=419)
            self.assertEqual(c,[])
            self.assertEqual(r['modules']['A']['status'],'not_attempted_budget')
            self.assertEqual(r['modules']['B']['blocker_statuses'],{'A':'not_attempted_budget'})
            self.assertEqual(r['modules']['C']['status'],'not_attempted_budget')
            self.assertFalse(r['dependency_ready_inventory_complete'])

    def test_audit_timeout_never_claims_acceptance(self):
        with tempfile.TemporaryDirectory() as t:
            r,c,_,_=self.sweep(Path(t),{'A':[]},audit_code=124)
            self.assertEqual(r['audit']['status'],'timeout');self.assertFalse(r['packet_acceptance'])

    def test_audit_missing_marker_fails(self):
        with tempfile.TemporaryDirectory() as t:
            f,d,o,l,r=self.fixture(Path(t),{'A':[]});compile_fn,c=self.compiler()
            def no_marker(*args):
                row=compile_fn(*args)
                if args[1] is None:(args[4]/'ExperimentAudit.log').write_text('no marker')
                return row
            inv.inventory(f,d,o,l,{},r,1000,no_marker,lambda:0)
            self.assertEqual(r['audit']['status'],'audit_failed')

    def test_no_budget_for_audit_is_distinct(self):
        with tempfile.TemporaryDirectory() as t:
            times=iter([0,900])
            r,c,_,_=self.sweep(Path(t),{'A':[]},clock=lambda:next(times))
            self.assertEqual(r['audit']['status'],'not_attempted_budget')
            self.assertEqual(c,['A'])

    def test_interruption_checkpoint_and_cleanup(self):
        with tempfile.TemporaryDirectory() as t:
            f,d,o,l,r=self.fixture(Path(t),{'A':[],'B':[]})
            def interrupt(source,target,*rest):
                target.write_text('partial');raise KeyboardInterrupt()
            with self.assertRaises(KeyboardInterrupt):inv.inventory(f,d,o,l,{},r,1000,interrupt,lambda:0)
            saved=json.loads((o/'INVENTORY.json').read_text())
            self.assertEqual(saved['status'],'INVENTORY_ERROR')
            self.assertFalse(saved['dependency_ready_inventory_complete'])
            self.assertFalse((o/'quarantine').exists());self.assertFalse(list(l.iterdir()))

    def test_stale_artifact_rejected_not_reused(self):
        with tempfile.TemporaryDirectory() as t:
            f,d,o,l,r=self.fixture(Path(t),{'A':[]});(l/'A.olean').write_text('stale')
            fn,c=self.compiler()
            with self.assertRaisesRegex(ValueError,'preexisting'):inv.inventory(f,d,o,l,{},r,1000,fn,lambda:0)
            self.assertEqual(c,[]);self.assertFalse((l/'A.olean').exists())

    def test_success_without_output_is_error(self):
        with tempfile.TemporaryDirectory() as t:
            f,d,o,l,r=self.fixture(Path(t),{'A':[]})
            with self.assertRaisesRegex(ValueError,'Missing olean'):
                inv.inventory(f,d,o,l,{},r,1000,lambda *a:{'exit_code':0},lambda:0)
            self.assertFalse(r['dependency_ready_inventory_complete'])

    def test_signal_not_labeled_type_error(self):
        with tempfile.TemporaryDirectory() as t:
            r,_,_,_=self.sweep(Path(t),{'A':[]},{'A':-9})
            self.assertEqual(r['modules']['A']['status'],'process_error')

    def test_atomic_json_no_temp_remains(self):
        with tempfile.TemporaryDirectory() as t:
            p=Path(t)/'INVENTORY.json';inv.save(p,{'a':1});self.assertEqual(json.loads(p.read_text()),{'a':1})
            self.assertFalse(p.with_suffix('.tmp').exists())

    def setup_fixture(self,root):
        f,d,o,l,r=self.fixture(root,{'A':[]})
        # run() deliberately requires a fresh output folder.
        import shutil;shutil.rmtree(o)
        args=SimpleNamespace(output=o,packet='packet',cache=root/'cache',deadline=1000,setup_ok=False)
        plan={'snapshot':'snapshot','base':'base','module_order':[],'dependencies':{},'upstream':[]}
        return f,d,args,plan

    def test_failed_source_setup_cannot_invoke_compiler_or_environment(self):
        with tempfile.TemporaryDirectory() as t:
            f,d,args,plan=self.setup_fixture(Path(t))
            with patch.object(exp,'packet',return_value=(f,d,set(),set())),patch.object(ci,'environment') as env,patch.object(inv,'inventory') as sweep:
                with self.assertRaisesRegex(ValueError,'setup did not succeed'):inv.run(args,plan)
                env.assert_not_called();sweep.assert_not_called()
            r=json.loads((args.output/'INVENTORY.json').read_text());self.assertEqual(r['modules']['A']['status'],'setup_error')

    def test_invalid_packet_never_compiles(self):
        with tempfile.TemporaryDirectory() as t:
            _,_,args,plan=self.setup_fixture(Path(t));args.setup_ok=True
            with patch.object(exp,'packet',side_effect=ValueError('source hash mismatch')),patch.object(ci,'environment') as env:
                with self.assertRaisesRegex(ValueError,'source hash mismatch'):inv.run(args,plan)
                env.assert_not_called()
            self.assertEqual(json.loads((args.output/'INVENTORY.json').read_text())['status'],'SETUP_ERROR')

    def test_invalid_baseline_never_compiles(self):
        with tempfile.TemporaryDirectory() as t:
            f,d,args,plan=self.setup_fixture(Path(t));args.setup_ok=True
            with patch.object(exp,'packet',return_value=(f,d,set(),set())),patch.object(exp,'restore_baseline',side_effect=ValueError('stale baseline')),patch.object(ci,'environment') as env:
                with self.assertRaisesRegex(ValueError,'stale baseline'):inv.run(args,plan)
                env.assert_not_called()

    def test_upstream_missing_no_fallback_compilation(self):
        with tempfile.TemporaryDirectory() as t:
            f,d,args,plan=self.setup_fixture(Path(t));args.setup_ok=True
            with patch.object(exp,'packet',return_value=(f,d,set(),{'Mathlib.Missing'})),patch.object(exp,'restore_baseline',return_value={}),patch.object(ci,'environment',return_value=({'LEAN_PATH':str(Path(t)/'none')},'pinned')),patch.object(ci,'ensure_official') as fallback,patch.object(inv,'inventory') as sweep:
                with self.assertRaisesRegex(ValueError,'Missing pinned upstream'):inv.run(args,plan)
                fallback.assert_not_called();sweep.assert_not_called()

    def project_environment_fixture(self, root):
        project = root / 'pinned-project'; project.mkdir()
        (project / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
        rev = 'a' * 40
        (project / 'lake-manifest.json').write_text(json.dumps({'packages': [{'name': 'fake', 'rev': rev}]}))
        package = project / '.lake/packages/fake'
        (package / '.lake/build/lib/lean').mkdir(parents=True)
        return project, package, rev

    def check_project_environment(self, failure=None):
        # Real ci.environment logic, synthetic sources and mocked Git/Lean only.
        with tempfile.TemporaryDirectory() as t:
            root = Path(t); f,d,args,plan = self.setup_fixture(root); args.setup_ok = True
            project,package,rev = self.project_environment_fixture(root)
            original = Path.cwd(); calls = []
            def output(command, **kwargs):
                calls.append(command)
                if command == ['git', 'rev-parse', 'HEAD']:
                    self.assertEqual(kwargs['cwd'], package); return rev + '\n'
                self.assertEqual(command, ['lean', '--version'])
                if Path.cwd() != project:
                    raise subprocess.CalledProcessError(1, command, stderr='no default toolchain configured')
                if failure == 'missing':
                    raise subprocess.CalledProcessError(1, command, stderr='pinned toolchain unavailable')
                return 'Lean (version 0.0.0, wrong)' if failure else 'Lean (version 4.35.0, commit eb6cafb7290e)'
            def clean(command, **kwargs):
                self.assertEqual(command, ['git', 'diff', '--quiet', 'HEAD', '--'])
                self.assertEqual(kwargs['cwd'], package); self.assertTrue(kwargs['check'])
            with patch.object(exp, 'packet', return_value=(f,d,set(),set())), patch.object(exp, 'restore_baseline', return_value={}), patch.object(ci, 'PROJECT', project), patch.object(ci.subprocess, 'check_output', side_effect=output), patch.object(ci.subprocess, 'run', side_effect=clean) as cleanliness, patch.object(inv, 'inventory') as sweep:
                # Demonstrate that the uncorrected repo-root call has no default.
                with self.assertRaises(subprocess.CalledProcessError): ci.environment(project, root/'unused')
                if failure:
                    with self.assertRaises((ValueError, subprocess.CalledProcessError)): inv.run(args,plan)
                    sweep.assert_not_called()
                    receipt=json.loads((args.output/'INVENTORY.json').read_text())
                    self.assertEqual(receipt['status'],'SETUP_ERROR')
                    self.assertEqual(receipt['modules']['A']['status'],'setup_error')
                    self.assertEqual(receipt['audit']['status'],'not_run')
                else:
                    inv.run(args,plan); sweep.assert_called_once()
                    env=sweep.call_args.args[4]
                    self.assertEqual(env['LEAN_PATH'],os.pathsep.join([str(args.output/'lib'),str(package/'.lake/build/lib/lean')]))
                self.assertEqual(cleanliness.call_count,2)
                self.assertEqual(calls.count(['lean','--version']),2)
            self.assertEqual(Path.cwd(),original)

    def test_no_default_toolchain_uses_real_pinned_project_environment(self):
        self.check_project_environment()

    def test_wrong_project_compiler_keeps_setup_failure_and_restores_cwd(self):
        self.check_project_environment('wrong')

    def test_missing_project_compiler_keeps_setup_failure_and_restores_cwd(self):
        self.check_project_environment('missing')

    def test_compile_timeout_kills_group_preserves_fixed_flags(self):
        with tempfile.TemporaryDirectory() as t:
            p=Path(t);source=p/'A.lean';source.write_text('module')
            process=Mock(pid=123);process.wait.side_effect=[subprocess.TimeoutExpired('lean',180),-9]
            with patch.object(inv.subprocess,'Popen',return_value=process) as popen,patch.object(inv.os,'killpg') as kill:
                row=inv.compile_once(source,p/'out/A.olean',p,{},p/'logs')
            self.assertTrue(row['timed_out']);self.assertEqual(row['exit_code'],124)
            self.assertEqual(popen.call_args.args[0][1:5],ci.FLAGS)
            self.assertEqual(process.wait.call_args_list[0].kwargs,{'timeout':180})
            kill.assert_called_once_with(123,inv.signal.SIGKILL)
            self.assertIn('WALL_CLOCK_LIMIT_EXCEEDED',(p/'logs/A.log').read_text())

    def test_hosted_guard_blocks_local_compilation(self):
        with patch.dict(os.environ,{'GITHUB_ACTIONS':'false'}),patch('sys.argv',['x','--packet','x','--cache','x','--output','x','--deadline','1','--selection-sha256','0'*64,'--setup-ok','true']),patch.object(ci,'check_sources') as check:
            with self.assertRaisesRegex(RuntimeError,'hosted-only'):inv.main()
            check.assert_not_called()

    def test_source_variant_identity_not_collapsed(self):
        with tempfile.TemporaryDirectory() as t:
            r,_,_,_=self.sweep(Path(t),{'A':[]})
            row=r['modules']['A'];self.assertEqual(row['occurrence'],'packet/A');self.assertEqual(len(row['source_sha256']),64)
            self.assertFalse(r['packet_acceptance'])

    def test_workflow_limits_and_no_binary_upload_or_acceptance_replacement(self):
        root=Path(__file__).resolve().parents[1]
        s=(root/'.github/workflows/progress-inventory.yml').read_text()
        self.assertNotIn('  workflow_dispatch:',s);self.assertIn('  push:',s)
        self.assertIn('      - add-quartic-318-326',s)
        self.assertIn('      - .github/inventory-requests/progress.json',s)
        self.assertIn('fetch-depth: 2',s)
        self.assertLess(s.index('id: request'),s.index('id: plan'))
        self.assertIn('group: progress-inventory-${{ github.ref }}',s)
        self.assertNotIn('group: progress-experiments-${{ github.ref }}',s)
        self.assertNotIn('group: progress-inventory-${{ github.sha }}',s)
        self.assertIn('cancel-in-progress: false',s);self.assertIn('max-parallel: 4',s)
        self.assertIn('timeout-minutes: ${{ matrix.job_minutes }}',s);self.assertIn('+ WINDOW_MINUTES * 60',s)
        self.assertNotIn('lake env',s);self.assertNotIn('continue-on-error:',s)
        self.assertIn("steps.dependency_sources.outcome == 'success' && steps.upstream.outcome == 'success'",s)
        upload=s.split('name: Preserve inventory receipts and logs',1)[1]
        self.assertIn('if: always()',upload);self.assertNotIn('/lib',upload);self.assertNotIn('/quarantine',upload)
        self.assertIn('/INVENTORY.json',upload)
        normal=(root/'.github/workflows/progress-experiments.yml').read_text()
        self.assertIn('scripts/test_progress_inventory.py',normal)
        self.assertIn('check_progress_experiment.py check --packet',normal)
        self.assertNotIn('check_progress_inventory.py --packet',normal)


class RequestTests(unittest.TestCase):
    def fixture(self, root):
        import validate_progress_inventory_request as request
        def git(*args):
            return subprocess.check_output(['git','-c','user.name=Fixture','-c','user.email=fixture@example.invalid',*args],cwd=root,stderr=subprocess.DEVNULL).decode().strip()
        git('init','-q')
        (root/'source.txt').write_text('exact implementation')
        git('add','.');git('commit','-qm','synthetic source')
        source=git('rev-parse','HEAD');tree=git('rev-parse','HEAD^{tree}')
        data={'schema':1,'source_commit':source,'source_tree':tree,'request_id':'bounded-001'}
        marker=root/request.MARKER;marker.parent.mkdir(parents=True);marker.write_text(json.dumps(data))
        git('add','.');git('commit','-qm','synthetic marker')
        head=git('rev-parse','HEAD')
        event={'before':source,'after':head,'ref':request.BRANCH,'forced':False,'deleted':False}
        env={'GITHUB_EVENT_NAME':'push','GITHUB_REF':request.BRANCH,'GITHUB_SHA':head}
        def amend():
            git('add','.');git('commit','--amend','--no-edit','-q')
            event['after']=env['GITHUB_SHA']=git('rev-parse','HEAD')
        return request,git,data,marker,event,env,amend

    def test_real_git_marker_only_commit_and_tree_binding(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);v,g,d,m,e,env,a=self.fixture(root)
            r=v.validate(root,e,env)
            self.assertEqual(r['source_commit'],d['source_commit']);self.assertEqual(r['source_tree'],d['source_tree'])
            self.assertTrue(r['unchanged_non_marker_tree']);self.assertFalse(r['proof_acceptance'])
            self.assertEqual(r['marker_sha256'],hashlib.sha256(m.read_bytes()).hexdigest())

    def test_wrong_event_branch_force_or_delete_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);v,g,d,m,e,env,a=self.fixture(root)
            for key,value,in_env in [('GITHUB_EVENT_NAME','workflow_dispatch',True),('GITHUB_REF','refs/heads/main',True),('ref','refs/heads/main',False),('forced',True,False),('deleted',True,False)]:
                with self.subTest(key=key):
                    ee=dict(e);en=dict(env);(en if in_env else ee)[key]=value
                    with self.assertRaises(ValueError):v.validate(root,ee,en)

    def test_uncommitted_marker_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);v,g,d,m,e,env,a=self.fixture(root);m.write_text('{}')
            with self.assertRaisesRegex(ValueError,'worktree or index'):v.validate(root,e,env)

    def test_wrong_parent_tree_and_request_schema_rejected(self):
        for key,value in [('source_commit','0'*40),('source_tree','0'*40),('schema',True),('request_id','shell;bad'),('extra','bad')]:
            with self.subTest(key=key),tempfile.TemporaryDirectory() as t:
                root=Path(t);v,g,d,m,e,env,a=self.fixture(root);d[key]=value;m.write_text(json.dumps(d));a()
                with self.assertRaises(ValueError):v.validate(root,e,env)

    def test_mixed_source_and_marker_commit_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);v,g,d,m,e,env,a=self.fixture(root);(root/'source.txt').write_text('different proof');a()
            with self.assertRaisesRegex(ValueError,'other than the request'):v.validate(root,e,env)

    def test_unstaged_source_mutation_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);v,g,d,m,e,env,a=self.fixture(root);(root/'source.txt').write_text('dirty uncommitted source')
            with self.assertRaisesRegex(ValueError,'worktree or index'):v.validate(root,e,env)

    def test_staged_source_mutation_rejected_even_if_worktree_restored(self):
        for restore_worktree in (False,True):
            with self.subTest(restored=restore_worktree),tempfile.TemporaryDirectory() as t:
                root=Path(t);v,g,d,m,e,env,a=self.fixture(root);(root/'source.txt').write_text('staged change');g('add','source.txt')
                if restore_worktree:(root/'source.txt').write_text('exact implementation')
                with self.assertRaisesRegex(ValueError,'worktree or index'):v.validate(root,e,env)

    def test_multiple_commit_push_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);v,g,d,m,e,env,a=self.fixture(root);e['before']='0'*40
            with self.assertRaisesRegex(ValueError,'exactly one'):v.validate(root,e,env)

    def test_duplicate_keys_and_executable_marker_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);v,g,d,m,e,env,a=self.fixture(root);m.write_text(json.dumps(d)[:-1]+',"schema":1}');a()
            with self.assertRaisesRegex(ValueError,'Duplicate'):v.validate(root,e,env)
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);v,g,d,m,e,env,a=self.fixture(root);m.chmod(0o755);a()
            with self.assertRaisesRegex(ValueError,'nonexecutable'):v.validate(root,e,env)

    def test_launch_path_excluded_from_both_production_filters(self):
        import fnmatch,re,validate_progress_inventory_request as v
        root=Path(__file__).resolve().parents[1]
        for name in ('progress-experiments.yml','progress-lean.yml'):
            s=(root/'.github/workflows'/name).read_text();push=s.split('  push:',1)[1].split('  pull_request:',1)[0].split('  workflow_dispatch:',1)[0]
            paths=re.findall(r"^      - '([^']+)'",push,re.M)
            self.assertTrue(paths)
            self.assertFalse(any(fnmatch.fnmatchcase(v.MARKER,p) for p in paths),name)
        workflow=(root/'.github/workflows/progress-inventory.yml').read_text()
        trigger=workflow.split('on:',1)[1].split('permissions:',1)[0]
        self.assertNotIn('scripts/',trigger);self.assertNotIn('.github/workflows/',trigger)
        self.assertIn(v.MARKER,trigger)


class ShardTests(unittest.TestCase):
    fixture = InventoryTests.fixture
    compiler = InventoryTests.compiler
    setup_fixture = InventoryTests.setup_fixture
    # Every compile is the synthetic compiler above.
    def test_closure_keeps_dependencies_skips_unrelated_prefix(self):
        from plan_progress_inventory import selection
        with tempfile.TemporaryDirectory() as t:
            f,d,o,l,r=self.fixture(Path(t),{'Old':[], 'A':[], 'B':['A'], 'C':['B'], 'Other':[]})
            chosen=selection('packet',ci.sha(f/'intake.json'),d,['C'])
            self.assertEqual(chosen['selected_order'],['A','B','C'])
            for n in d['order']:
                if n not in chosen['selected_order']:r['modules'][n]['status']='not_selected'
            fn,calls=self.compiler()
            inv.inventory(f,d,o,l,{},r,1000,fn,lambda:0)
            self.assertEqual(calls,['A','B','C','ExperimentAudit'])
            self.assertEqual(r['counts'],{'not_selected':2,'compile_pass':3})
            self.assertTrue(r['selected_dependency_ready_inventory_complete'])
            self.assertFalse(r['dependency_ready_inventory_complete'])
            self.assertFalse(r['all_packet_modules_compiled'])
            self.assertFalse(r['packet_acceptance'])
            self.assertEqual(r['audit']['modules'],['A','B','C'])

    def test_selection_deterministic_and_exact_intake_bound(self):
        from plan_progress_inventory import selection
        with tempfile.TemporaryDirectory() as t:
            f,d,_,_,_=self.fixture(Path(t),{'A':[], 'B':[], 'C':['A']})
            a=selection('packet','1'*64,d,['C','B'])
            self.assertEqual(a,selection('packet','1'*64,d,['B','C']))
            self.assertNotEqual(a['selection_sha256'],selection('packet','2'*64,d,['C','B'])['selection_sha256'])
            self.assertEqual(a['targets'],['B','C'])
            for targets in ([],['Missing'],['A','A'],'A',[True]):
                with self.subTest(targets=targets),self.assertRaises(ValueError):selection('packet','1'*64,d,targets)

    def test_selected_budget_blockers_not_omitted_or_failure(self):
        with tempfile.TemporaryDirectory() as t:
            f,d,o,l,r=self.fixture(Path(t),{'Old':[], 'A':[], 'B':['A']})
            r['modules']['Old']['status']='not_selected';fn,calls=self.compiler()
            inv.inventory(f,d,o,l,{},r,419,fn,lambda:0)
            self.assertEqual(calls,[])
            self.assertEqual(r['modules']['B']['blocker_statuses'],{'A':'not_attempted_budget'})
            self.assertEqual(r['modules']['Old']['status'],'not_selected')
            self.assertFalse(r['selected_dependency_ready_inventory_complete'])

    def test_selection_hash_mismatch_fails_before_environment(self):
        with tempfile.TemporaryDirectory() as t:
            f,d,args,plan=self.setup_fixture(Path(t));args.setup_ok=True;args.selection_sha256='0'*64
            with patch.object(exp,'packet',return_value=(f,d,set(),set())),patch.object(ci,'environment') as environment:
                with self.assertRaisesRegex(ValueError,'Selection identity'):inv.run(args,plan)
                environment.assert_not_called()

    def test_targeted_setup_failure_preserves_not_selected(self):
        with tempfile.TemporaryDirectory() as t:
            f,d,args,plan=self.setup_fixture(Path(t));args.targets=['A']
            d['order'].append('Other');d['files']['Other.lean']={'sha256':'0'*64,'imports':[]}
            with patch.object(exp,'packet',return_value=(f,d,set(),set())):
                with self.assertRaisesRegex(ValueError,'setup did not succeed'):inv.run(args,plan)
            rows=json.loads((args.output/'INVENTORY.json').read_text())['modules']
            self.assertEqual(rows['Other']['status'],'not_selected');self.assertEqual(rows['A']['status'],'setup_error')

    def test_plan_full_validation_and_active_scope(self):
        from plan_progress_inventory import build
        with tempfile.TemporaryDirectory() as t:
            f,d,_,_,_=self.fixture(Path(t),{'A':[], 'B':['A'], 'Other':[]})
            req={'schema':2,'source_commit':'1'*40,'source_tree':'2'*40,'request_id':'shard',
                 'job_minutes':210,'shards':[{'packet':'packet','targets':['B']},{'packet':'packet','targets':['Other']}]}
            packet=Mock(return_value=(f,d,set(),set()));publication=Mock()
            plan={'base':'base','snapshot':'snapshot'}
            result=build(req,plan,['packet'],packet,publication)
            packet.assert_called_once_with('packet',plan);publication.assert_called_once_with([f])
            rows=result['matrix']['include'];self.assertEqual(len(rows),2)
            self.assertNotEqual(rows[0]['artifact_key'],rows[1]['artifact_key'])
            self.assertEqual(rows[0]['job_minutes'],210);self.assertEqual(rows[0]['window_minutes'],204)
            self.assertEqual(json.loads(rows[0]['targets_json']),['B'])
            with self.assertRaisesRegex(ValueError,'not active'):build(req,plan,[],packet,publication)
            packet.side_effect=ValueError('full packet hash mismatch')
            with self.assertRaisesRegex(ValueError,'full packet hash mismatch'):build(req,plan,['packet'],packet,publication)

    def test_schema1_preserves_full_packet_window_and_artifact_name(self):
        from plan_progress_inventory import build
        with tempfile.TemporaryDirectory() as t:
            f,d,_,_,_=self.fixture(Path(t),{'A':[]})
            req={'schema':1,'source_commit':'1'*40,'source_tree':'2'*40,'request_id':'old'}
            result=build(req,{'base':'b','snapshot':'s'},['packet'],lambda *a:(f,d,set(),set()),lambda *a:None)
            row=result['matrix']['include'][0]
            self.assertEqual(row['targets_json'],'null');self.assertEqual(row['artifact_key'],'packet')
            self.assertEqual((row['job_minutes'],row['window_minutes']),(30,24))

    def test_schema2_shape_rejects_unbounded_or_ambiguous_requests(self):
        from validate_progress_inventory_request import validate_shape
        original={'schema':2,'source_commit':'1'*40,'source_tree':'2'*40,'request_id':'new',
                  'job_minutes':210,'shards':[{'packet':'packet','targets':['A']}]}
        validate_shape(original)
        changes=[{'job_minutes':True},{'job_minutes':211},{'job_minutes':29},{'shards':[]},
                 {'shards':original['shards']*17},{'shards':original['shards']*2},
                 {'shards':[{'packet':'../bad','targets':None}]},
                 {'shards':[{'packet':'packet','targets':[]}]},
                 {'shards':[{'packet':'packet','targets':['A','A']}]},
                 {'shards':[{'packet':'packet','targets':['A;bad']}]},
                 {'shards':[{'packet':'packet','targets':['A'+str(i) for i in range(65)]}]},
                 {'extra':True}]
        for change in changes:
            with self.subTest(change=change),self.assertRaises(ValueError):validate_shape({**original,**change})

    def test_hosted_long_deadline_still_bounded(self):
        argv=['x','--packet','x','--cache','x','--output','x','--deadline','12241',
              '--window-minutes','204','--selection-sha256','0'*64,'--setup-ok','true']
        with patch.dict(os.environ,{'GITHUB_ACTIONS':'true'}),patch('sys.argv',argv),patch.object(inv.time,'time',return_value=0),patch.object(ci,'check_sources') as check:
            with self.assertRaisesRegex(ValueError,'bounded inventory'):inv.main()
            check.assert_not_called()

    def test_no_shard_implementation_in_production_check(self):
        root=Path(__file__).resolve().parents[1]
        production=(root/'scripts/check_progress_experiment.py').read_text()
        self.assertNotIn('not_selected',production)
        self.assertNotIn('targets_json',production)
        workflow=(root/'.github/workflows/progress-inventory.yml').read_text()
        self.assertIn('--selection-sha256 "$SELECTION_SHA256"',workflow)
        self.assertIn('--targets-json "$TARGETS_JSON"',workflow)
        self.assertIn('name: inventory-${{ matrix.artifact_key }}',workflow)
        self.assertIn('scripts/plan_progress_inventory.py',workflow)
        self.assertNotIn('download-artifact',workflow)
        self.assertNotIn('cache/save',workflow)


class ShardRequestTests(unittest.TestCase):
    fixture = RequestTests.fixture
    def test_real_git_schema2_source_binding(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);v,g,d,m,e,env,a=self.fixture(root)
            d.update(schema=2,job_minutes=210,shards=[{'packet':'packet','targets':['A']}])
            m.write_text(json.dumps(d));a();r=v.validate(root,e,env)
            self.assertEqual(r['shards'],d['shards']);self.assertEqual(r['source_commit'],d['source_commit'])
            self.assertFalse(r['proof_acceptance'])
            (root/'source.txt').write_text('dirty shard compiler')
            with self.assertRaisesRegex(ValueError,'worktree or index'):v.validate(root,e,env)


if __name__=='__main__':
    # These mocked observation guards run during planning; they never invoke Lean.
    from test_zero72_prefixes import GuardTests as Zero72GuardTests, FrozenPrefixTests
    unittest.main()
