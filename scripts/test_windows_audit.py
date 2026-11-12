#!/usr/bin/env python3
"""Small adapter tests; they do not invoke Lean or perform an audit."""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_progress_lean as ci
import windows_audit as audit

class ToolchainTests(unittest.TestCase):
    def test_requires_real_installed_binary(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
            with self.assertRaisesRegex(RuntimeError, 'not installed'):
                audit.installed_toolchain_bin(root, root)
            bindir = root / 'toolchains/leanprover--lean4---v4.35.0/bin'
            bindir.mkdir(parents=True)
            (bindir / 'lean.exe').write_bytes(b'fixture')
            self.assertEqual(audit.installed_toolchain_bin(root, root), bindir)

    def test_discovery_precedence_and_explicit_failure(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            project, repo, user = root / 'project', root / 'repo', root / 'user'
            project.mkdir()
            (project / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
            def install(home):
                b = home / 'toolchains/leanprover--lean4---v4.35.0/bin'
                b.mkdir(parents=True)
                (b / 'lean.exe').write_bytes(b'fixture')
                return b.resolve()
            default = install(user / '.elan')
            self.assertEqual(audit.resolve_toolchain_bin(project, repo, user_home=user), default)
            local = install(repo / 'audit-tools/elan')
            self.assertEqual(audit.resolve_toolchain_bin(project, repo, user_home=user), local)
            explicit = install(root / 'custom')
            self.assertEqual(audit.resolve_toolchain_bin(project, repo, root / 'custom', user), explicit)
            with self.assertRaisesRegex(RuntimeError, 'not installed'):
                audit.resolve_toolchain_bin(project, repo, root / 'missing', user)

    def test_discovery_missing_reports_locations(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
            with self.assertRaisesRegex(RuntimeError, 'Set ELAN_HOME'):
                audit.resolve_toolchain_bin(root, root / 'repo', user_home=root / 'user')

class WorkerTests(unittest.TestCase):
    def setUp(self):
        self.original_digest, self.original_flags = ci.digest, ci.FLAGS
        self.original_official, self.original_run = ci.ensure_official, subprocess.run
        self.original_add_argument = argparse.ArgumentParser.add_argument
        spec = importlib.util.spec_from_file_location('windows_audit_worker_test', Path(__file__).with_name('windows_audit_worker.py'))
        self.worker = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.worker)

    def tearDown(self):
        ci.digest, ci.FLAGS = self.original_digest, self.original_flags
        ci.ensure_official, subprocess.run = self.original_official, self.original_run
        argparse.ArgumentParser.add_argument = self.original_add_argument

    def test_identity_and_flags(self):
        value = {'platform': 'linux-x86_64', 'example': 'value'}
        self.assertNotEqual(ci.digest(value), self.original_digest(value))
        self.assertEqual(ci.digest({'unrelated': 1}), self.original_digest({'unrelated': 1}))
        self.assertEqual(ci.FLAGS, ['-j1', '-Ddebug.skipKernelTC=false'])

    def test_local_cohort_count_supports_more_than_32_cpus(self):
        parser = argparse.ArgumentParser()
        with patch('os.cpu_count', return_value=64):
            parser.add_argument('--cohorts', type=int, choices=range(1, 33))
        self.assertEqual(parser.parse_args(['--cohorts', '64']).cohorts, 64)

    def test_timeout_removed(self):
        seen = {}
        def fake(*args, **kwargs):
            seen.update(kwargs)
        self.worker._original_run = fake
        subprocess.run(['example'], timeout=600)
        self.assertIsNone(seen['timeout'])

    def test_lean_commands_use_selected_binary_including_check_output(self):
        selected = str(Path(tempfile.gettempdir()) / 'selected' / 'lean.exe')
        seen = []
        def fake(args, **kwargs):
            seen.append(args)
            return subprocess.CompletedProcess(args, 0, stdout='lean version')
        self.worker._original_run = fake
        with patch.dict('os.environ', {'QUARTIC_WINDOWS_LEAN_EXE': selected}):
            subprocess.run(['lean', '--version'])
            self.assertEqual(subprocess.check_output(['lean', '--version'], text=True), 'lean version')
            subprocess.run(['git', '--version'])
        self.assertEqual(seen[0][0], selected)
        self.assertEqual(seen[1][0], selected)
        self.assertEqual(seen[2][0], 'git')

    def test_missing_upstream_is_error_not_a_build(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)
            (p / 'lake-manifest.json').write_text(json.dumps({'packages': []}))
            (p / 'checkpoint-manifest.json').write_text(json.dumps({'module_order': []}))
            with self.assertRaisesRegex(RuntimeError, 'Missing upstream artifacts'):
                ci.ensure_official(p, {}, p)

if __name__ == '__main__':
    unittest.main()
