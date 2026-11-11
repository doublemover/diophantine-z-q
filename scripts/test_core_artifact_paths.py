#!/usr/bin/env python3
"""Guard retained core diagnostics against stale literal revision paths."""
import ast
import fnmatch
from pathlib import Path
import unittest
ROOT = Path(__file__).resolve().parents[1]
class CoreArtifactPaths(unittest.TestCase):
    def test_current_guard_artifacts_retained(self):
        tree = ast.parse((ROOT / 'scripts/check_source_word_core_smoke.py').read_text())
        core = next(ast.literal_eval(n.value) for n in tree.body if isinstance(n, ast.Assign)
                    and any(isinstance(t, ast.Name) and t.id == 'CORE' for t in n.targets))
        workflow = (ROOT / '.github/workflows/progress-experiments.yml').read_text()
        paths = [line.strip() for line in workflow.splitlines()
                 if line.strip().startswith('build/progress-experiments/relative-varying-source-word-core-')]
        for suffix in ['RESULT.json', 'logs/', 'ExperimentAudit.lean', 'SMOKE_SCOPE.json']:
            target = f'build/progress-experiments/{core}/{suffix}'
            self.assertTrue(any(fnmatch.fnmatchcase(target, pattern) for pattern in paths), target)
        self.assertEqual(len(paths), 4)
        self.assertFalse(any('**' in p for p in paths))
    def test_workflow_runs_regression(self):
        workflow = (ROOT / '.github/workflows/progress-experiments.yml').read_text()
        self.assertIn('python -B scripts/test_core_artifact_paths.py', workflow)
if __name__ == '__main__':
    unittest.main()
