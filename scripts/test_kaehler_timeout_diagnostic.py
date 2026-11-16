"""Pure source/guard tests. Never invokes Lean."""
import importlib.util
import os
from pathlib import Path
import sys
import unittest
from unittest.mock import patch
HERE=Path(__file__).resolve().parent
if not (HERE/'check_progress_lean.py').exists():
    sys.path.insert(0,str(HERE.parent/'recovery-focused-replay/scripts'))
spec=importlib.util.spec_from_file_location('kaehler',HERE/'diagnose_kaehler_timeout.py')
d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d)
class Tests(unittest.TestCase):
    def source(self):
        return (HERE/'diagnostic_evidence/kaehler_timeout_source.lean.txt').read_text()
    def test_exact_specimens(self):
        out=d.control_specimens(self.source())
        self.assertEqual({k:d.digest(v) for k,v in out.items()},d.CONTROL_SCRATCH_SHAS)
        for value in out.values():
            self.assertLess(value.index('set_option stderrAsMessages false'),value.index('run_cmd'))
        self.assertEqual(out['command_trace'].count('KAEHLER_COMMAND_'),21)
    def test_scoped_substep_instrumentation(self):
        text=d.control_specimens(self.source())['command_trace']
        self.assertEqual(text.count(d.SUBSTEP_SCOPE),1)
        self.assertEqual(text.count(d.SUBSTEP_TACTIC_DECL),1)
        self.assertLess(text.index(d.SUBSTEP_TACTIC_DECL),text.index(d.SUBSTEP_SCOPE))
        self.assertNotIn('run_tac',text)
        self.assertIn('Lean.Elab.Tactic.evalTactic rwTac',d.SUBSTEP_TACTIC_DECL)
        self.assertIn('Lean.Elab.Tactic.evalTactic rflTac',d.SUBSTEP_TACTIC_DECL)
        self.assertIn(d.SUBSTEP_SCOPE+'lemma source_coordinate_original:',text)
        self.assertEqual(text.count(d.SUBSTEP_FINAL_TACTICS.rstrip('\n')),1)
        self.assertEqual(text.count('Lean.Elab.Tactic.evalTactic'),2)
        for label in ['BEFORE_FINAL_RW','AFTER_FINAL_RW','BEFORE_FINAL_RFL','AFTER_FINAL_RFL']:
            self.assertEqual(text.count('emit "'+label+'"'),1)
        self.assertLess(text.index('emit "BEFORE_FINAL_RW"'),text.index('emit "AFTER_FINAL_RW"'))
        self.assertLess(text.index('emit "BEFORE_FINAL_RFL"'),text.index('emit "AFTER_FINAL_RFL"'))
        # Undo only the instrumentation; exact old frozen diagnostic is restored.
        restored=text.replace(d.SUBSTEP_TACTIC_DECL,'',1).replace(d.SUBSTEP_SCOPE,'',1).replace(d.SUBSTEP_FINAL_TACTICS.rstrip('\n'),d.OLD_FINAL_TACTICS.rstrip('\n'),1)
        self.assertEqual(d.digest(restored),'324766ba3fac040b7055810250f3b2639b45786f04729f2b6c7417a41f460955')
    def test_substep_boundaries_fail_closed(self):
        text=d.control_specimens(self.source())['command_trace']
        original=text.replace(d.SUBSTEP_TACTIC_DECL,'',1).replace(d.SUBSTEP_SCOPE,'',1).replace(d.SUBSTEP_FINAL_TACTICS.rstrip('\n'),d.OLD_FINAL_TACTICS.rstrip('\n'),1)
        for changed in [original.replace('lemma source_coordinate_original:','lemma moved:',1), original.replace(d.OLD_FINAL_TACTICS.rstrip('\n'),'  exact False.elim (by contradiction)',1)]:
            with self.assertRaises(ValueError):d.substep_specimen(changed)
    def test_tamper_rejected(self):
        with self.assertRaisesRegex(ValueError,'Frozen target source changed'):d.specimens(self.source()+'\n')
    def test_hosted_guard(self):
        with patch.dict(os.environ,{'GITHUB_ACTIONS':'false'},clear=True):
            with self.assertRaisesRegex(ValueError,'Hosted Actions only'):d.validate(Path('/missing'),Path('/missing'))
    def test_main_guard_before_writes(self):
        with patch.dict(os.environ,{'GITHUB_ACTIONS':'false'},clear=True),patch.object(sys,'argv',['diagnostic',d.PACKET]):
            with self.assertRaisesRegex(ValueError,'Hosted Actions only'):d.main()
    def test_fixed_runner_limits(self):
        self.assertEqual(tuple(d.ci.FLAGS),d.EXPECTED_FLAGS)
        self.assertEqual(d.runner.original.SECONDS,90)
        self.assertEqual(d.runner.original.MAX_BYTES,2*1024*1024)
        self.assertEqual(d.sha(Path(d.runner.__file__)),d.RUNNER_SHA)
        self.assertEqual(d.sha(Path(d.runner.original.__file__)),d.RUNNER_LIMITS_SHA)
    def test_workflow_exact_hook_and_upload(self):
        workflow=(HERE.parent/'.github/workflows/progress-experiments.yml').read_text()
        self.assertIn('      - run: python -B scripts/test_kaehler_timeout_diagnostic.py',workflow)
        self.assertEqual(workflow.count('lake env python -B ../../../../scripts/diagnose_kaehler_timeout.py'),1)
        hook=workflow.split('      - name: Non-admitted exact Kaehler')[1].split('      - name: Upload')[0]
        self.assertIn("matrix.packet == '"+d.PACKET+"'",hook)
        self.assertIn("steps.dependency_sources.outcome == 'success'",hook)
        self.assertIn('build/progress-experiments/${{ matrix.packet }}/scratch-kaehler-timeout/',workflow)

    def test_candidate_exact_reversible_source_scope(self):
        candidate=d.frozen_candidate(self.source())
        self.assertEqual(d.digest(candidate),d.CANDIDATE_SOURCE_SHA)
        restored=candidate.replace(d.GENERIC_HELPER,'',1).replace(d.SQUARE_HELPER,'',1).replace(d.TRANSPORT_HELPER,'',1).replace(d.CANDIDATE_TARGET_PROOF,d.ORIGINAL_TARGET_PROOF,1).replace(d.CANDIDATE_SQUARE_PROOF,d.ORIGINAL_SQUARE_PROOF,1).replace(d.CANDIDATE_REGROUP_PROOF,d.ORIGINAL_REGROUP_PROOF,1)
        self.assertEqual(restored,self.source())
        self.assertEqual(candidate.count('private theorem tensorScalarImage'),1)
    def test_direct_term_proof_scope(self):
        proof=d.CANDIDATE_TARGET_PROOF
        self.assertIn('(sourceLocalizationEquiv b i).symm_apply_eq.mpr',proof)
        self.assertIn('sourceLocalizationEquiv_on_source b i',proof)
        self.assertNotIn('  apply ',proof)
        self.assertNotIn('  rw ',proof)
        self.assertNotIn('  change ',proof)
        self.assertEqual(self.source().count(d.ORIGINAL_TARGET_PROOF),1)
        self.assertEqual(d.frozen_candidate(self.source()).count(proof),1)
    def test_original_square_proof_scope(self):
        proof=d.CANDIDATE_SQUARE_PROOF
        self.assertIn('FourRootAffineCoordinateRing318.relation b i',proof)
        self.assertIn('(source_coordinate_original b i).symm',proof)
        self.assertNotIn('  apply ',proof)
        self.assertNotIn('  rw ',proof)
        self.assertNotIn('  change ',proof)
        self.assertEqual(self.source().count(d.ORIGINAL_SQUARE_PROOF),1)
        text=d.candidate_specimen(d.frozen_candidate(self.source()))
        self.assertIn(d.SUBSTEP_SCOPE+'lemma exact_square:',text)
        self.assertLess(text.index('KAEHLER_CANDIDATE_BEFORE_MAPPED_SQUARE'),text.index('KAEHLER_CANDIDATE_AFTER_MAPPED_SQUARE'))
    def test_doc_comments_are_not_split_by_trace_options(self):
        candidate=d.frozen_candidate(self.source())
        target='lemma source_coordinate_original:'
        prefix=candidate[:candidate.index(target)]
        doc=prefix[prefix.rfind('/--'):]
        text=d.candidate_specimen(d.frozen_candidate(self.source()))
        self.assertIn(d.SUBSTEP_SCOPE+doc+target,text)
        self.assertNotIn(doc+d.SUBSTEP_SCOPE+target,text)
    def test_scope_declaration_boundaries(self):
        target='lemma example:'
        plain=target+' True := by trivial\n'
        documented='/-- attached doc -/\n'+plain
        self.assertEqual(d.scope_declaration(plain,target),d.SUBSTEP_SCOPE+plain)
        self.assertEqual(d.scope_declaration(documented,target),d.SUBSTEP_SCOPE+documented)
        with self.assertRaises(ValueError):d.scope_declaration(plain+plain,target)
    def test_syntax_corrections_are_explicit_and_reversible(self):
        self.assertNotIn('⊗[',d.GENERIC_HELPER)
        self.assertIn('TensorProduct R A B',d.GENERIC_HELPER)
        self.assertNotIn('change _ (',d.CANDIDATE_REGROUP_PROOF)
        self.assertEqual(self.source().count(d.ORIGINAL_REGROUP_PROOF),1)
    def test_compiler_outcome_never_admits_or_certifies_checkpoints(self):
        self.assertEqual(d.compiler_outcome({'exit_code':0,'limit':None}),'EXIT_ZERO_NO_AUDIT_OR_ADMISSION')
        self.assertEqual(d.compiler_outcome({'exit_code':1,'limit':None}),'COMPILER_FAILURE_NO_ACCEPTANCE')
        self.assertEqual(d.compiler_outcome({'exit_code':-9,'limit':'SCRATCH_WALL_LIMIT'}),'LIMIT_REACHED_NO_ACCEPTANCE')
        source=(HERE/'diagnose_kaehler_timeout.py').read_text()
        self.assertNotIn('getMessages',source)
        self.assertIn("'checkpoints_are_traversal_only':True",source)
        self.assertIn("'timeouts_may_hide_deferred_errors':True",source)
    def test_candidate_two_probe_budget_and_hashes(self):
        out=d.specimens(self.source())
        self.assertEqual(list(out),['imports_only','complete_candidate_prefix'])
        self.assertEqual({k:d.digest(v) for k,v in out.items()},d.SCRATCH_SHAS)
        self.assertEqual(out['imports_only'],d.control_specimens(self.source())['imports_only'])
        self.assertEqual(d.SECONDS,90);self.assertEqual(d.MAX_BYTES,2*1024*1024)
    def test_candidate_instrumentation_and_reversal(self):
        import re
        candidate=d.frozen_candidate(self.source());text=d.candidate_specimen(d.frozen_candidate(self.source()))
        self.assertEqual(text.count('KAEHLER_CANDIDATE_'),27)
        self.assertEqual(text.count(d.SUBSTEP_SCOPE),5)
        self.assertNotIn('kaehler_final',text)
        self.assertNotIn('run_tac',text)
        # Remove only diagnostic markers/options, then restore original checkpoints.
        pattern=r'run_cmd Lean.Elab.Command.liftIO do\n  let out ← IO.getStderr\n  out.putStrLn "KAEHLER_CANDIDATE_([^"]+)"\n  out.flush'
        for label in ['BEFORE_GENERIC_HELPER','AFTER_GENERIC_HELPER','BEFORE_MAPPED_SQUARE','AFTER_MAPPED_SQUARE','BEFORE_TRANSPORT_HELPER','AFTER_TRANSPORT_HELPER']:
            block='run_cmd Lean.Elab.Command.liftIO do\n  let out ← IO.getStderr\n  out.putStrLn "KAEHLER_CANDIDATE_'+label+'"\n  out.flush\n'
            text=text.replace(block,'',1)
        def checkpoint(m):return '#eval (do\n  let out ← IO.getStdout\n  out.putStrLn "PEL_KAEHLER_CHECKPOINT '+m[1]+'"\n  out.flush : IO Unit)'
        text=re.sub(pattern,checkpoint,text).replace(d.SUBSTEP_SCOPE,'').replace('set_option stderrAsMessages false\n','',1).replace('set_option profiler true\nset_option profiler.threshold 10\n','',1)
        self.assertEqual(text,candidate)
    def test_candidate_tamper_fails_closed(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'candidate.txt';path.write_text(d.CANDIDATE_FIXTURE.read_text()+'\n')
            with patch.object(d,'CANDIDATE_FIXTURE',path):
                with self.assertRaisesRegex(ValueError,'Reviewed candidate changed'):d.specimens(self.source())
        with self.assertRaisesRegex(ValueError,'Reviewed candidate changed'):d.candidate_specimen('bad')
    def test_original_authentication_and_runtime_core_unchanged(self):
        import ast,hashlib
        source=(HERE/'diagnose_kaehler_timeout.py').read_text();tree=ast.parse(source)
        expected={'no_compiled': '8f344b5bdf2b1f08f3ed7d66aa1540806788caf92adef9baed47741c1e8adebb', 'baseline_dependency_evidence': '7c9da57f5d34bf330f6d2d17ca7df38b5ba87f104fe72440c7fed07b790407e4', 'validate': 'dbce238559d75795fa197f8e079a5608c3d5459de86712e4c103406264a57d79'}
        for node in tree.body:
            if isinstance(node,(ast.FunctionDef,ast.AsyncFunctionDef)) and node.name in expected:
                self.assertEqual(hashlib.sha256(ast.get_source_segment(source,node).encode()).hexdigest(),expected[node.name])
        self.assertIn("'candidate_source_sha256':CANDIDATE_SOURCE_SHA",source)
        self.assertIn('probe_wall_cap_sum_seconds=2*SECONDS',source)
        self.assertIn("'full_packet_accepted':False,'proof_acceptance':False,'writes_olean':False",source)

    def test_complete_prefix_exact_boundary_and_namespace(self):
        candidate=d.frozen_candidate(self.source())
        raw=candidate[:candidate.index(d.PREFIX_CHECKPOINT)]
        self.assertEqual(d.digest(raw),d.PREFIX_RAW_SHA)
        out=d.specimens(self.source())['complete_candidate_prefix']
        full=d.candidate_specimen(candidate)
        self.assertEqual(out,full[:full.index(d.PREFIX_MARKER)]+d.PREFIX_END)
        self.assertTrue(out.endswith(d.PREFIX_END))
        self.assertIn('private def transportedRegroup',out)
        self.assertIn('private theorem transportedRegroupRoot',out)
        self.assertNotIn('variable (b:Fin 4',out)
        for excluded in ['lemma source_coordinate_original:', 'lemma exact_square:', 'def sourceParameter', 'KAEHLER_CANDIDATE_before_source_coordinate_original']:
            self.assertNotIn(excluded,out)
        self.assertNotIn('/-- The exact original source coordinate',out)
    def test_complete_prefix_tamper_rejected(self):
        candidate=d.frozen_candidate(self.source())
        with self.assertRaises(ValueError):d.prefix_specimen(candidate+'\n')
        with patch.object(d,'PREFIX_RAW_SHA','0'*64):
            with self.assertRaisesRegex(ValueError,'raw prefix changed'):d.prefix_specimen(candidate)
        with patch.object(d,'PREFIX_MARKER',d.PREFIX_MARKER+'missing'):
            with self.assertRaisesRegex(ValueError,'Instrumented prefix'):d.prefix_specimen(candidate)
    def test_prefix_metadata_does_not_claim_full_candidate(self):
        source=(HERE/'diagnose_kaehler_timeout.py').read_text()
        self.assertIn("'target_declaration_included':False",source)
        self.assertIn("'prefix_last_declaration':'transportedRegroupRoot'",source)
        self.assertIn('not original production',source)
        self.assertIn('neither the target/full candidate nor production audit',source)

    def test_transport_helper_preserves_equality_transports(self):
        helper=d.TRANSPORT_HELPER
        self.assertIn('rw [hp,hq]\n  exact FourRootPivot318.regroup a i',helper)
        self.assertIn('(transportedRegroup a i p q hp hq)',helper)
        self.assertIn('subst p\n  subst q',helper)
        self.assertIn('ActualRootPivotCoordinates318.regroup_generator a i',helper)
        self.assertIn('exact transportedRegroupRoot',d.CANDIDATE_REGROUP_PROOF)
        self.assertIn('h0 hother',d.CANDIDATE_REGROUP_PROOF)
        text=d.specimens(self.source())['complete_candidate_prefix']
        self.assertEqual(text.count('private theorem transportedRegroupRoot'),1)
        self.assertEqual(text.count('private def transportedRegroup'),1)
        self.assertIn('KAEHLER_CANDIDATE_BEFORE_TRANSPORT_HELPER',text)
        self.assertIn('KAEHLER_CANDIDATE_AFTER_TRANSPORT_HELPER',text)

    def test_transport_helper_dictionary_arguments_are_explicit(self):
        helper=d.TRANSPORT_HELPER
        self.assertIn('(@algebraMap (QuadraticPresentation318.RootRing p)',helper)
        self.assertIn('(inferInstance : CommSemiring (QuadraticPresentation318.RootRing p))',helper)
        self.assertIn('(inferInstance : Semiring',helper)
        self.assertIn('inferInstance)\n        (AdjoinRoot.root',helper)

    def test_compatibility_prefix_has_no_concrete_variables(self):
        candidate=d.frozen_candidate(self.source())
        raw=candidate[:candidate.index(d.PREFIX_CHECKPOINT)]
        self.assertEqual(len(raw.encode()),3316)
        self.assertEqual(d.digest(raw),'bd4cff194761fa3a02fee3566b2667fecc66d5389bf4dd27c26dc878eda9bad2')
        out=d.specimens(self.source())['complete_candidate_prefix']
        self.assertIn('rw [hp,hq]\n  exact FourRootPivot318.regroup a i',out)
        for absent in ['lemma regroup_root','variable (b:Fin 4','sorry','axiom ']:
            self.assertNotIn(absent,out)
        self.assertTrue(out.rstrip().endswith('end FourRootActualBranchKaehler318'))

    def test_compatibility_theorem_is_complete_at_boundary(self):
        out=d.specimens(self.source())['complete_candidate_prefix']
        self.assertIn('subst p\n  subst q\n  exact ActualRootPivotCoordinates318.regroup_generator a i',out)
        self.assertLess(out.index('private theorem transportedRegroupRoot'),out.index('KAEHLER_CANDIDATE_AFTER_TRANSPORT_HELPER'))
        self.assertNotIn('local instance regrouped_commRing',out)

    def baseline_fixture(self, root):
        # Synthetic artifact bytes test authentication, never Lean compilation.
        import hashlib, json
        project = root / 'project'; project.mkdir()
        source = (d.ci.PROJECT / 'SquareCoordinateDifferential318.lean').read_bytes()
        (project / 'SquareCoordinateDifferential318.lean').write_bytes(source)
        name = 'SquareCoordinateDifferential318'; parent = 'BaselineParent'
        plan = {'snapshot': 'snapshot', 'base': 'base', 'module_order': [parent, name],
            'module_keys': {parent: 'parent-key', name: 'square-key'},
            'dependencies': {parent: [], name: [parent]}}
        cache = root / '.cache/progress-ci'; (cache / 'lib').mkdir(parents=True)
        output = root / 'output'; (output / 'lib').mkdir(parents=True)
        entries = {}
        for module in plan['module_order']:
            data = ('synthetic-not-compiled-' + module).encode()
            for lib in [cache / 'lib', output / 'lib']:
                (lib / (module + '.olean')).write_bytes(data)
            entries[module] = {'key': plan['module_keys'][module],
                'files': {'.olean': hashlib.sha256(data).hexdigest()},
                'dependency_artifacts': {n: entries[n]['files'] for n in plan['dependencies'][module]}}
        receipt = {'schema': d.ci.SCHEMA, 'status': 'PASS', 'base': plan['base'],
            'snapshot': plan['snapshot'], 'scope': 'Complete source coverage and recursive axiom audit',
            'audit_result_sha256': 'a' * 64, 'modules': entries}
        (cache / 'receipt.json').write_text(json.dumps(receipt))
        result = {'baseline_snapshot': plan['snapshot'], 'baseline_modules': 2}
        return project, output, plan, receipt, result

    def check_baseline_fixture(self, root, fixture):
        project, output, plan, receipt, result = fixture
        with patch.object(d.ci, 'ROOT', root), patch.object(d.ci, 'PROJECT', project), \
             patch.object(d.ci, 'derive_plan', return_value=plan):
            return d.baseline_dependency_evidence(output, result,
                d.DEPENDENCIES - set(d.BASELINE_SOURCES))

    def test_actual_baseline_origin_and_packet_split(self):
        import json
        plan = d.ci.derive_plan()
        name = 'SquareCoordinateDifferential318'
        self.assertIn(name, plan['module_keys'])
        self.assertEqual(d.sha(d.ci.PROJECT / (name + '.lean')), d.BASELINE_SOURCES[name])
        self.assertEqual(plan['dependencies'][name], [])
        packet = d.ci.ROOT / 'quartics/quartic-318-326/proof/experiments' / d.PACKET
        intake = json.loads((packet / 'intake.json').read_text())
        prefix = set(intake['order'][:intake['order'].index(d.MODULE)])
        self.assertEqual(d.DEPENDENCIES - prefix, set(d.BASELINE_SOURCES))
        self.assertNotIn(name + '.lean', intake['files'])

    def test_authenticated_baseline_closure_read_only(self):
        import tempfile
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder); fixture = self.baseline_fixture(root)
            before = {str(p.relative_to(root)): p.read_bytes() for p in root.rglob('*') if p.is_file()}
            evidence = self.check_baseline_fixture(root, fixture)
            self.assertEqual(evidence['required_modules'], ['BaselineParent', 'SquareCoordinateDifferential318'])
            self.assertEqual(len(evidence['same_run_artifacts']), 2)
            self.assertEqual(evidence['scope'], 'AUTHENTICATED_REUSED_BASELINE_NOT_FRESH_COMPILATION')
            after = {str(p.relative_to(root)): p.read_bytes() for p in root.rglob('*') if p.is_file()}
            self.assertEqual(before, after)

    def test_baseline_fails_closed_on_tampering(self):
        import tempfile, json
        cases = ['source', 'normal_snapshot', 'normal_module_count', 'receipt_status', 'receipt_scope',
                 'receipt_base', 'receipt_snapshot', 'audit_reference', 'module_key',
                 'dependency_chain', 'cached_artifact', 'copied_artifact', 'missing_parent',
                 'extra_copied_artifact', 'missing_baseline_membership']
        for case in cases:
            with self.subTest(case=case), tempfile.TemporaryDirectory() as folder:
                root = Path(folder); fixture = self.baseline_fixture(root)
                project, output, plan, receipt, result = fixture
                name = 'SquareCoordinateDifferential318'; cache = root / '.cache/progress-ci'
                if case == 'source': (project / (name + '.lean')).write_text('changed')
                elif case == 'normal_snapshot': result['baseline_snapshot'] = 'other'
                elif case == 'normal_module_count': result['baseline_modules'] = 3
                elif case.startswith('receipt_'): receipt[case.removeprefix('receipt_')] = 'wrong'
                elif case == 'audit_reference': receipt.pop('audit_result_sha256')
                elif case == 'module_key': receipt['modules'][name]['key'] = 'wrong'
                elif case == 'dependency_chain': receipt['modules'][name]['dependency_artifacts'] = {}
                elif case == 'cached_artifact': (cache / 'lib' / (name + '.olean')).write_bytes(b'wrong')
                elif case == 'copied_artifact': (output / 'lib' / (name + '.olean')).write_bytes(b'wrong')
                elif case == 'missing_parent': receipt['modules'].pop('BaselineParent')
                elif case == 'extra_copied_artifact': (output / 'lib' / (name + '.olean.private')).write_bytes(b'extra')
                elif case == 'missing_baseline_membership': plan['module_keys'].pop(name)
                (cache / 'receipt.json').write_text(json.dumps(receipt))
                with self.assertRaises((ValueError, OSError)):
                    self.check_baseline_fixture(root, fixture)

    def test_missing_experiment_import_not_treated_as_baseline(self):
        import tempfile
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder); fixture = self.baseline_fixture(root)
            project, output, plan, receipt, result = fixture
            with patch.object(d.ci, 'ROOT', root), patch.object(d.ci, 'PROJECT', project), \
                 patch.object(d.ci, 'derive_plan', return_value=plan):
                with self.assertRaisesRegex(ValueError, 'Unexpected dependency'):
                    d.baseline_dependency_evidence(output, result, [])

if __name__=='__main__':unittest.main()
