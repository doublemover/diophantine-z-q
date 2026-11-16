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
        out=d.specimens(self.source())
        self.assertEqual({k:d.digest(v) for k,v in out.items()},d.SCRATCH_SHAS)
        for value in out.values():
            self.assertLess(value.index('set_option stderrAsMessages false'),value.index('run_cmd'))
        self.assertEqual(out['command_trace'].count('KAEHLER_COMMAND_'),21)
    def test_scoped_substep_instrumentation(self):
        text=d.specimens(self.source())['command_trace']
        self.assertEqual(text.count(d.SUBSTEP_SCOPE),1)
        self.assertIn(d.SUBSTEP_SCOPE+'lemma source_coordinate_original:',text)
        self.assertEqual(text.count(d.SUBSTEP_FINAL_TACTICS.rstrip('\n')),1)
        self.assertEqual(text.count('Lean.Elab.Tactic.evalTactic'),2)
        for label in ['BEFORE_FINAL_RW','AFTER_FINAL_RW','BEFORE_FINAL_RFL','AFTER_FINAL_RFL']:
            self.assertEqual(text.count('emit "'+label+'"'),1)
        self.assertLess(text.index('emit "BEFORE_FINAL_RW"'),text.index('emit "AFTER_FINAL_RW"'))
        self.assertLess(text.index('emit "BEFORE_FINAL_RFL"'),text.index('emit "AFTER_FINAL_RFL"'))
        # Undo only the instrumentation; exact old frozen diagnostic is restored.
        restored=text.replace(d.SUBSTEP_SCOPE,'',1).replace(d.SUBSTEP_FINAL_TACTICS.rstrip('\n'),d.OLD_FINAL_TACTICS.rstrip('\n'),1)
        self.assertEqual(d.digest(restored),'324766ba3fac040b7055810250f3b2639b45786f04729f2b6c7417a41f460955')
    def test_substep_boundaries_fail_closed(self):
        text=d.specimens(self.source())['command_trace']
        original=text.replace(d.SUBSTEP_SCOPE,'',1).replace(d.SUBSTEP_FINAL_TACTICS.rstrip('\n'),d.OLD_FINAL_TACTICS.rstrip('\n'),1)
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
