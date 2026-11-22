#!/usr/bin/env python3
"""Deterministic fixtures: no network, Lake installation, or Lean execution."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

import inventory_mathlib_cache as cache


ARCHIVE = '0123456789abcdef.ltar'
BODY = b'LTR3' + bytes(8) + b'archive fixture'
ROOTS = b'Mathlib.Algebra.Group.Basic\nMathlib.Init\n'


class InventoryMathlibCacheTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.transport = cache.cache_path(self.root)
        self.key = 'inventory-mathlib-ltar-v1-Linux-X64-ubuntu24-' + cache.digest(ROOTS)
        self.project = self.root / 'proof'
        self.project.mkdir()
        self.targets = self.root / 'targets.txt'
        self.targets.write_bytes(ROOTS)
        (self.project / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
        (self.project / 'lakefile.toml').write_text('name = "test"\n')
        (self.project / 'lake-manifest.json').write_text(json.dumps({
            'packagesDir': '.lake/packages', 'lakeDir': '.lake',
            'packages': [{'name': 'mathlib', 'type': 'git', 'url': 'https://github.com/' + cache.CANONICAL,
                          'rev': '1' * 40, 'manifestFile': 'lake-manifest.json', 'configFile': 'lakefile.lean'}],
        }))
        self.log = self.root / 'setup' / 'native.log'

    def native(self, output=cache.NATIVE_ALL + '\n', code=0, *, name=ARCHIVE, mutate=False):
        def run(command, project, env):
            self.assertEqual(command, ['lake', 'exe', 'cache', 'get-', '--repo=' + cache.CANONICAL,
                                       '--cache-from=master', *ROOTS.decode().splitlines()])
            self.assertEqual(project, self.project)
            self.assertNotIn('MATHLIB_CACHE_GET_URL', env)
            self.assertNotIn('MATHLIB_CACHE_DEBUG_USE_LEGACY', env)
            self.assertNotIn('LEAN_PATH', env)
            staging = Path(env['MATHLIB_CACHE_DIR'])
            self.assertNotEqual(staging, self.transport)
            self.assertEqual(list(staging.iterdir()), [])
            (staging / name).write_bytes(BODY)
            if mutate:
                (project / 'lakefile.toml').write_text('name = "mutated"\n')
            return subprocess.CompletedProcess(command, code, output.encode())
        return run

    def warm(self, run=None):
        return cache.warm(self.transport, self.key, self.project, self.targets, self.log,
                          run=run or self.native())

    def rejected(self):
        self.assertEqual(cache.use_restore(self.transport, self.key, 'true')['status'], 'rejected')
        self.assertFalse(os.path.lexists(self.transport))

    def test_warm_and_exact_worker_hit(self):
        with mock.patch.dict(os.environ, {'MATHLIB_CACHE_GET_URL': 'https://example.invalid',
                                          'MATHLIB_CACHE_DEBUG_USE_LEGACY': 'true',
                                          'MATHLIB_CACHE_DIR': '/nonexistent', 'LEAN_PATH': 'override'}):
            self.assertEqual(self.warm(), {'status': 'ready', 'targets': 2, 'files': 1, 'bytes': len(BODY)})
        self.assertEqual(self.log.read_text(), cache.NATIVE_ALL + '\n')
        self.assertEqual(cache.use_restore(self.transport, self.key, 'true'),
                         {'status': 'ready', 'exact_cache_hit': True, 'files': 1, 'bytes': len(BODY)})
        self.assertEqual((self.transport / ARCHIVE).read_bytes(), BODY)

    def test_catalog_for_wrong_identity_rejected(self):
        self.warm()
        previous = self.key
        self.key = 'other-exact-platform-' + cache.key_target_sha(previous)
        self.rejected()

    def test_same_length_body_corruption_rejected(self):
        self.warm()
        (self.transport / ARCHIVE).write_bytes(BODY[:-1] + b'X')
        self.rejected()

    def test_missing_archive_rejected(self):
        self.warm()
        (self.transport / ARCHIVE).unlink()
        self.rejected()

    def test_unexpected_native_executable_or_folder_rejected(self):
        for name in ('curl-7.88.1', '.lake', 'extra.log'):
            with self.subTest(name=name):
                self.warm()
                unexpected = self.transport / name
                if name == '.lake':
                    unexpected.mkdir()
                else:
                    unexpected.write_text('no')
                self.rejected()

    def test_canonical_named_archive_symlink_rejected_without_following(self):
        self.warm()
        outside = self.root / 'outside.ltar'
        outside.write_bytes(BODY)
        (self.transport / ARCHIVE).unlink()
        (self.transport / ARCHIVE).symlink_to(outside)
        self.rejected()
        self.assertEqual(outside.read_bytes(), BODY)

    def test_catalog_symlink_rejected_without_following(self):
        self.warm()
        cat = self.transport / cache.CATALOG
        outside = self.root / 'outside.json'
        cat.rename(outside)
        cat.symlink_to(outside)
        self.rejected()
        self.assertTrue(outside.is_file())

    def test_symlink_cache_root_rejected_without_following(self):
        self.warm()
        outside = self.root / 'outside'
        self.transport.rename(outside)
        self.transport.symlink_to(outside, target_is_directory=True)
        self.rejected()
        self.assertTrue((outside / ARCHIVE).is_file())

    def test_duplicate_catalog_key_rejected(self):
        self.warm()
        p = self.transport / cache.CATALOG
        original = p.read_text()
        p.write_text(original.replace('{"cache_key":', '{"schema":1, "cache_key":', 1))
        self.rejected()

    def test_soft_miss_and_partial_restore_cleared(self):
        for hit in ('', 'false'):
            with self.subTest(hit=hit):
                self.transport.mkdir()
                (self.transport / ARCHIVE).write_bytes(BODY[:3])
                self.assertEqual(cache.use_restore(self.transport, self.key, hit),
                                 {'status': 'missing', 'exact_cache_hit': False})
                self.assertFalse(self.transport.exists())

    def test_zero_exit_missing_native_sentinel_does_not_publish(self):
        with self.assertRaisesRegex(ValueError, 'complete upstream download'):
            self.warm(self.native('Downloaded all available files (1 not in the cache).\n'))
        self.assertFalse(self.transport.exists())

    def test_nonzero_exit_with_success_text_does_not_publish(self):
        with self.assertRaisesRegex(ValueError, 'complete upstream download'):
            self.warm(self.native(code=7))
        self.assertFalse(self.transport.exists())

    def test_unexpected_successful_native_file_not_published(self):
        with self.assertRaisesRegex(ValueError, 'Unexpected Mathlib cache filename'):
            self.warm(self.native(name='cache-cfg'))
        self.assertFalse(self.transport.exists())

    def test_lock_change_after_get_does_not_publish(self):
        with self.assertRaisesRegex(ValueError, 'Lock inputs changed'):
            self.warm(self.native(mutate=True))
        self.assertFalse(self.transport.exists())

    def test_rejects_wrong_target_hash_before_subprocess(self):
        self.targets.write_bytes(b'Mathlib.Init\n')
        run = mock.Mock()
        with self.assertRaisesRegex(ValueError, 'SHA-256'):
            self.warm(run)
        run.assert_not_called()

    def test_rejects_invalid_targets_even_if_cache_key_binds_them(self):
        for invalid in (b'--unsafe\n', b'Mathlib/Init.lean\n', b'Mathlib.Init\nMathlib.Init\n',
                        b'Mathlib.Init\nMathlib.Algebra.Group.Basic\n'):
            with self.subTest(invalid=invalid):
                self.targets.write_bytes(invalid)
                with self.assertRaisesRegex(ValueError, 'sorted unique'):
                    cache.read_targets(self.targets, 'key-' + cache.digest(invalid))

    def test_actual_cli_reports_ready_and_soft_rejects(self):
        self.warm()
        status = self.root / 'github-output'
        env = {**os.environ, 'RUNNER_TEMP': str(self.root), 'GITHUB_WORKSPACE': str(self.root),
               'GITHUB_OUTPUT': str(status)}
        command = [sys.executable, '-B', str(Path(cache.__file__)), 'restore',
                   '--cache-key', self.key, '--cache-hit', 'true']
        first = subprocess.run(command, check=True, capture_output=True, env=env, text=True)
        self.assertEqual(json.loads(first.stdout)['status'], 'ready')
        (self.transport / ARCHIVE).write_bytes(b'bad')
        second = subprocess.run(command, check=True, capture_output=True, env=env, text=True)
        self.assertEqual(json.loads(second.stdout)['status'], 'rejected')
        self.assertEqual(status.read_text(), 'status=ready\nstatus=rejected\n')
        self.assertFalse(self.transport.exists())


if __name__ == '__main__':
    unittest.main()
