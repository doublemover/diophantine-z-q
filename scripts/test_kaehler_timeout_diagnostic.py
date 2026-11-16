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
if __name__=='__main__':unittest.main()
