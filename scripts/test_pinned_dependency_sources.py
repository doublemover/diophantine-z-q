"""Source-cache trust and bounded retry controls. Synthetic local Git only; no Lean."""
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import pinned_dependency_sources as s

ROOT = Path(__file__).resolve().parents[1]


class SourceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.origin = self.root / 'origin'; self.origin.mkdir()
        s.checked(s.git(self.origin, 'init', '--template='))
        for key, value in [('user.email', 'test@example.invalid'), ('user.name', 'test')]:
            s.checked(s.git(self.origin, 'config', key, value))
        (self.origin / 'lakefile.toml').write_text('name = "test"\n')
        (self.origin / 'A.lean').write_text('-- original source\n')
        s.checked(s.git(self.origin, 'add', '.')); s.checked(s.git(self.origin, 'commit', '-m', 'first'))
        (self.origin / 'A.lean').write_text('-- second source\n')
        s.checked(s.git(self.origin, 'commit', '-am', 'second'))
        self.rev = s.checked(s.git(self.origin, 'rev-parse', 'HEAD')).decode().strip()
        self.project = self.root / 'project'; self.project.mkdir()
        package = {'name': 'test', 'url': 'https://github.com/example/test', 'rev': self.rev,
                   'type': 'git', 'subDir': None, 'manifestFile': 'lake-manifest.json', 'configFile': 'lakefile.toml'}
        self.package = package
        (self.project / 'lake-manifest.json').write_text(json.dumps({'packagesDir': '.lake/packages', 'lakeDir': '.lake', 'packages': [package]}))
        (self.project / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
        (self.project / 'lakefile.toml').write_text('name = "fixture"\n')
        self.cache = self.root / 'cache'; self.log = self.root / 'log'
        self.real_acquire = s.acquire

    def mock_acquire(self, args, *rest):
        # Only this test redirects the exact remote argument to our synthetic repo.
        args = [self.origin.as_uri() if a == self.package['url'] else a for a in args]
        return self.real_acquire(args, *rest, sleeper=lambda _: None)

    def setup_sources(self):
        receipt = {'attempts': []}
        with patch.object(s, 'acquire', self.mock_acquire):
            s.sources(self.project, self.cache, receipt, self.log)
        return receipt

    def test_cold_then_warm_exact_bytes_no_network_and_no_cached_git_config(self):
        first = self.setup_sources(); self.assertEqual(first['cache'], 'source-miss-verified')
        self.assertEqual(set(p.name for p in self.cache.iterdir()), {'identity.json', 'test.bundle'})
        target = self.project / '.lake/packages/test'
        self.assertEqual((target / 'A.lean').read_text(), '-- second source\n')
        (target / 'A.lean').write_text('dirty')
        (target / 'injected.olean').write_text('not proof evidence')
        (target / '.git/config').write_text('[core]\n hooksPath = /bad\n')
        with patch.object(s, 'acquire', side_effect=AssertionError('network on warm hit')):
            r = {'attempts': []}; s.sources(self.project, self.cache, r, self.log)
        self.assertEqual(r['cache'], 'verified-source-hit')
        self.assertFalse((target / 'injected.olean').exists())
        self.assertNotIn('/bad', (target / '.git/config').read_text())
        self.assertEqual(s.verify_checkout(target, self.package), 2)

    def test_corrupt_bundle_fails_before_lake(self):
        self.setup_sources(); (self.cache / 'test.bundle').write_bytes(b'bad')
        with self.assertRaises(RuntimeError): self.setup_sources()

    def test_wrong_commit_bundle_rejected(self):
        self.setup_sources()
        first = s.checked(s.git(self.origin, 'rev-parse', 'HEAD^')).decode().strip()
        s.checked(s.git(self.origin, 'checkout', '--detach', first))
        (self.cache / 'test.bundle').unlink()
        s.checked(s.git(self.origin, 'bundle', 'create', str(self.cache / 'test.bundle'), 'HEAD'))
        with self.assertRaises((ValueError, RuntimeError)): self.setup_sources()

    def test_wrong_lock_toolchain_and_helper_identity_rejected(self):
        self.setup_sources()
        for key in ['lake-manifest.json', 'lean-toolchain', 'lakefile.toml', 'helper_sha256']:
            p = self.cache / 'identity.json'; old = p.read_text(); d = json.loads(old); d[key] = 'wrong'; p.write_text(json.dumps(d))
            with self.assertRaises(ValueError): self.setup_sources()
            p.write_text(old)

    def test_extra_cache_entry_and_symlink_rejected(self):
        self.setup_sources(); extra = self.cache / 'bad.olean'; extra.write_text('bad')
        with self.assertRaises(ValueError): self.setup_sources()
        extra.unlink(); bundle = self.cache / 'test.bundle'; other = self.root / 'other'; bundle.rename(other); bundle.symlink_to(other)
        with self.assertRaises(ValueError): self.setup_sources()

    def test_dirty_untracked_worktree_is_not_verified(self):
        self.setup_sources(); target = self.project / '.lake/packages/test'
        (target / 'A.lean').write_text('dirty')
        with self.assertRaises(ValueError): s.verify_checkout(target, self.package)
        (target / 'A.lean').write_text('-- second source\n'); (target / 'untracked').write_text('x')
        with self.assertRaises(ValueError): s.verify_checkout(target, self.package)

    def test_compiled_tracked_source_is_rejected(self):
        self.setup_sources(); target = self.project / '.lake/packages/test'
        s.checked(s.git(target, 'config', 'user.email', 'test@example.invalid')); s.checked(s.git(target, 'config', 'user.name', 'test'))
        prior = None
        for suffix in ['.olean', '.olean.private', '.olean.server', '.ilean', '.ir', '.o', '.so', '.dll', '.dylib', '.a', '.obj', '.exe', '.bc']:
            with self.subTest(suffix=suffix):
                if prior is not None:
                    prior.unlink()
                prior = target / ('bad' + suffix); prior.write_bytes(b'x')
                s.checked(s.git(target, 'add', '-A')); s.checked(s.git(target, 'commit', '-m', 'fixture ' + suffix))
                pkg = dict(self.package, rev=s.checked(s.git(target, 'rev-parse', 'HEAD')).decode().strip())
                with self.assertRaisesRegex(ValueError, 'Compiled artifact'):
                    s.verify_checkout(target, pkg)

    def test_escaping_tracked_symlink_rejected(self):
        (self.origin / 'escape').symlink_to('/tmp/outside-source-cache')
        s.checked(s.git(self.origin, 'add', '.')); s.checked(s.git(self.origin, 'commit', '-m', 'escape'))
        self.package['rev'] = s.checked(s.git(self.origin, 'rev-parse', 'HEAD')).decode().strip()
        p = self.project / 'lake-manifest.json'; data = json.loads(p.read_text()); data['packages'] = [self.package]; p.write_text(json.dumps(data))
        with self.assertRaises(ValueError): self.setup_sources()

    def test_bundle_extra_replace_refs_never_imported(self):
        self.setup_sources()
        other = s.checked(s.git(self.origin, 'rev-parse', 'HEAD^')).decode().strip()
        s.checked(s.git(self.origin, 'update-ref', 'refs/replace/' + self.rev, other))
        s.checked(s.git(self.origin, 'update-ref', 'refs/heads/unexpected', other))
        bundle = self.cache / 'test.bundle'; bundle.unlink()
        s.checked(s.git(self.origin, 'bundle', 'create', str(bundle), 'HEAD', '--all'))
        with patch.object(s, 'acquire', side_effect=AssertionError('network on hit')):
            r = {'attempts': []}; s.sources(self.project, self.cache, r, self.log)
        target = self.project / '.lake/packages/test'
        refs = s.checked(s.git(target, 'for-each-ref')).decode()
        self.assertEqual(refs, '')
        self.assertEqual((target / 'A.lean').read_text(), '-- second source\n')

    def test_unsafe_manifest_fields(self):
        p = self.project / 'lake-manifest.json'; old = json.loads(p.read_text())
        for key, value in [('name', '../escape'), ('url', 'file:///tmp/bad'), ('rev', 'main'), ('subDir', '../escape'), ('configFile', '../x')]:
            data = json.loads(json.dumps(old)); data['packages'][0][key] = value; p.write_text(json.dumps(data))
            with self.assertRaises(ValueError): s.lock(self.project)
        p.write_text(json.dumps(old))

    def test_failure_receipt_and_final_exit_preserved(self):
        receipt = self.root / 'failure.json'
        args = ['pinned_dependency_sources.py', 'sources', '--project', str(self.project), '--cache', str(self.cache), '--receipt', str(receipt)]
        with patch('sys.argv', args), patch.object(s, 'sources', side_effect=s.AcquisitionError(128, 'test')):
            self.assertEqual(s.main(), 128)
        self.assertEqual(json.loads(receipt.read_text())['status'], 'FAIL')
        self.assertFalse(json.loads(receipt.read_text())['proof_check_run'])


class RetryTests(unittest.TestCase):
    def call(self, outputs):
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        receipt = {'attempts': []}; runner = unittest.mock.Mock(side_effect=outputs); sleep = unittest.mock.Mock()
        return receipt, runner, sleep, Path(tmp.name) / 'attempts.log'

    def test_transient_503_then_success(self):
        r, run, sleep, log = self.call([subprocess.CompletedProcess([], 128, b'fatal: requested URL returned error: 503'), subprocess.CompletedProcess([], 0, b'ok')])
        s.acquire(['git'], 'test', r, log, run, sleep)
        self.assertEqual(run.call_count, 2); sleep.assert_called_once_with(5); self.assertIn(b'503', log.read_bytes())

    def test_exhaustion_three_attempts_keeps_exit_and_output(self):
        r, run, sleep, log = self.call([subprocess.CompletedProcess([], 128, b'requested URL returned error: 503')] * 3)
        with self.assertRaises(s.AcquisitionError) as e: s.acquire(['git'], 'test', r, log, run, sleep)
        self.assertEqual(e.exception.code, 128); self.assertEqual(run.call_count, 3); self.assertEqual(sleep.call_count, 2)
        self.assertEqual(log.read_bytes().count(b'503'), 3)

    def test_compiler_and_nontransient_errors_not_retried(self):
        for output in [b'A.lean:1:1: error: bad\nHTTP 503', b'unknown revision', b'checksum mismatch']:
            r, run, sleep, log = self.call([subprocess.CompletedProcess([], 1, output)])
            with self.assertRaises(s.AcquisitionError): s.acquire(['git'], 'test', r, log, run, sleep)
            self.assertEqual(run.call_count, 1); sleep.assert_not_called()

    def test_timeout_is_bounded_and_receipted(self):
        r, run, sleep, log = self.call([subprocess.TimeoutExpired(['git'], 180)] * 3)
        with self.assertRaises(s.AcquisitionError) as e: s.acquire(['git'], 'test', r, log, run, sleep)
        self.assertEqual(e.exception.code, 124); self.assertEqual(len(r['attempts']), 3)


class WorkflowTests(unittest.TestCase):
    def test_exact_key_and_source_only_action(self):
        a = (ROOT / '.github/actions/setup-pinned-dependency-sources/action.yml').read_text()
        self.assertNotIn('restore-keys:', a)
        for name in ['lake-manifest.json', 'lean-toolchain', 'lakefile.toml', 'pinned_dependency_sources.py']:
            self.assertEqual(a.count(name), 2 if name != 'pinned_dependency_sources.py' else 3)
        self.assertNotIn('progress-ci', a); self.assertNotIn('path: .lake', a)
        self.assertLess(a.index('Reconstruct and verify'), a.index('Save verified'))

    def test_failure_diagnostics_cannot_bypass_source_validation(self):
        w = (ROOT / '.github/workflows/progress-experiments.yml').read_text()
        def audit(text):
            steps = re.split(r'(?m)^      - ', text.split('  first-check:', 1)[1])
            validated = False
            consumers = 0
            for step in steps:
                if 'id: dependency_sources' in step:
                    validated = True
                if 'lake ' not in step and 'pinned_dependency_sources.py artifacts' not in step:
                    continue
                consumers += 1
                if not validated:
                    raise AssertionError('Lake consumer precedes source validation')
                cond = re.search(r'(?m)^        if: (.+)$', step)
                # With setup failed, default success() is false. Explicit
                # always()/failure() must additionally require source success.
                if cond and "steps.dependency_sources.outcome == 'success'" not in cond.group(1):
                    raise AssertionError('Failure-path Lake consumer can bypass validation')
            return consumers
        self.assertGreater(audit(w), 20)
        guard = "steps.dependency_sources.outcome == 'success' && "
        with self.assertRaises(AssertionError): audit(w.replace(guard, '', 1))
        with self.assertRaises(AssertionError): audit(w.replace("failure() && " + guard, 'failure() && '))
        self.assertIn('name: dependency-setup-${{ matrix.packet }}', w)
        self.assertIn('if: always()\n        uses: actions/upload-artifact@', w)

    def test_strict_checks_still_once_and_unmodified(self):
        w = (ROOT / '.github/workflows/progress-experiments.yml').read_text()
        self.assertEqual(w.count('check_progress_experiment.py check --packet'), 1)
        self.assertIn('--seconds 180', w)
        self.assertIn('cancel-in-progress: false', w)
        self.assertIn('&& 4 || 8', w)
        self.assertIn('timeout-minutes: 30', w)
        self.assertLess(w.index('Warm verified dependency sources'), w.index('  first-check:'))
        self.assertIn('dependency-setup-${{ matrix.packet }}', w)
        self.assertNotIn('lake update', w)


if __name__ == '__main__':
    unittest.main()
