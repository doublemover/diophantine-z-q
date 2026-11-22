#!/usr/bin/env python3
"""Optional transport for pinned native Mathlib .ltar downloads.

Only a trusted, source-validated plan job creates the catalog. Its hashes check
transport integrity, not the authenticity of a new upstream producer. Workers
still reconstruct exact sources, use native cache get, and run the existing
baseline, kernel and axiom checks. No .lake or project output is shared here.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import stat
import subprocess
import tempfile
import time

import pinned_dependency_sources as pinned


DIRECTORY = 'inventory-mathlib'
CATALOG = 'catalog.json'
SCHEMA = 1
TIMEOUT = 180
KEY = re.compile(r'[A-Za-z0-9_-]{1,447}-([0-9a-f]{64})')
LTAR = re.compile(r'[0-9a-f]{16}\.ltar')
TARGET = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*')
MAX_CATALOG = 8 * 1024 * 1024
NATIVE_ALL = 'Downloaded all files successfully!'
CANONICAL = 'leanprover-community/mathlib4'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def key_target_sha(key):
    match = KEY.fullmatch(key)
    if not match:
        raise ValueError('Invalid exact Mathlib key or missing target SHA-256 suffix')
    return match[1]


def cache_path(runner_temp):
    if not runner_temp.is_absolute() or not runner_temp.is_dir():
        raise ValueError('RUNNER_TEMP must be an existing absolute directory')
    return runner_temp.resolve(strict=True) / DIRECTORY


def remove_entry(path):
    """Remove the isolated transport path without following symlinks."""
    try:
        mode = path.lstat().st_mode
    except FileNotFoundError:
        return
    if stat.S_ISDIR(mode):
        shutil.rmtree(path)
    else:
        path.unlink()


def regular_open(path):
    """Don't follow links or open FIFOs from a restored entry."""
    if not stat.S_ISREG(path.lstat().st_mode):
        raise ValueError('Not a regular Mathlib cache file: ' + path.name)
    return os.fdopen(os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK), 'rb')


def archive_entry(path):
    if not LTAR.fullmatch(path.name):
        raise ValueError('Unexpected Mathlib cache filename: ' + path.name)
    with regular_open(path) as f:
        st = os.fstat(f.fileno())
        if not stat.S_ISREG(st.st_mode):
            raise ValueError('Not a regular Mathlib archive: ' + path.name)
        header = f.read(12)
        if len(header) != 12 or header[:4] not in (b'LTAR', b'LTR2', b'LTR3'):
            raise ValueError('Invalid Mathlib archive header: ' + path.name)
        sha = hashlib.sha256(header)
        size = len(header)
        while chunk := f.read(1024 * 1024):
            sha.update(chunk)
            size += len(chunk)
        if size != st.st_size:
            raise ValueError('Mathlib archive size changed during hashing: ' + path.name)
    return {'sha256': sha.hexdigest(), 'size': size}


def archives(path, with_catalog):
    if not stat.S_ISDIR(path.lstat().st_mode):
        raise ValueError('Mathlib transport path is not a regular directory')
    files = {entry.name: archive_entry(entry) for entry in sorted(path.iterdir())
             if not (with_catalog and entry.name == CATALOG)}
    if not files:
        raise ValueError('No Mathlib archives')
    return files


def unique_object(pairs):
    data = {}
    for key, value in pairs:
        if key in data:
            raise ValueError('Duplicate Mathlib catalog key: ' + key)
        data[key] = value
    return data


def describe(key, files):
    return {'schema': SCHEMA, 'cache_key': key, 'targets_sha256': key_target_sha(key),
            'upstream': CANONICAL, 'files': files}


def verify(path, key):
    # Reject a symlink root before opening even the catalog.
    if not stat.S_ISDIR(path.lstat().st_mode):
        raise ValueError('Mathlib transport path is not a regular directory')
    with regular_open(path / CATALOG) as f:
        st = os.fstat(f.fileno())
        if not stat.S_ISREG(st.st_mode) or not 0 < st.st_size <= MAX_CATALOG:
            raise ValueError('Not a bounded regular Mathlib catalog')
        raw = f.read(MAX_CATALOG + 1)
        if len(raw) != st.st_size:
            raise ValueError('Mathlib catalog size changed during read')
    got = json.loads(raw, object_pairs_hook=unique_object)
    if not isinstance(got, dict) or type(got.get('schema')) is not int:
        raise ValueError('Invalid Mathlib catalog schema')
    expected = describe(key, None)
    if set(got) != set(expected) or any(got[k] != v for k, v in expected.items() if k != 'files'):
        raise ValueError('Mathlib catalog identity differs from the exact request')
    files = got['files']
    if not isinstance(files, dict) or not files:
        raise ValueError('Invalid Mathlib catalog file list')
    for name, entry in files.items():
        if (not LTAR.fullmatch(name) or not isinstance(entry, dict) or set(entry) != {'sha256', 'size'}
                or type(entry['size']) is not int or entry['size'] < 12
                or not isinstance(entry['sha256'], str) or not re.fullmatch('[0-9a-f]{64}', entry['sha256'])):
            raise ValueError('Invalid Mathlib catalog entry: ' + name)
    if files != archives(path, with_catalog=True):
        raise ValueError('Mathlib catalog does not match actual archives')
    return files


def metrics(files):
    return {'files': len(files), 'bytes': sum(f['size'] for f in files.values())}


def use_restore(path, key, hit):
    if hit != 'true':
        remove_entry(path)
        return {'status': 'missing', 'exact_cache_hit': False}
    try:
        return {'status': 'ready', 'exact_cache_hit': True, **metrics(verify(path, key))}
    except (ValueError, OSError, RecursionError) as error:
        # GitHub cache entries are immutable. Don't try to overwrite a bad
        # exact key. The matrix worker uses its separately isolated fallback.
        remove_entry(path)
        return {'status': 'rejected', 'exact_cache_hit': True, 'reason': str(error)}


def read_targets(path, key):
    with path.open('rb') as f:
        raw = f.read(1024 * 1024 + 1)
    if len(raw) > 1024 * 1024 or digest(raw) != key_target_sha(key):
        raise ValueError('Upstream targets differ from exact cache-key SHA-256')
    roots = raw.decode('ascii').splitlines()
    if (not roots or len(roots) > 16384 or roots != sorted(set(roots))
            or any(not TARGET.fullmatch(x) for x in roots)):
        raise ValueError('Expected sorted unique Lean module names')
    return roots


def native_run(command, project, env):
    """One bounded optional warm attempt; don't leak a child curl on timeout."""
    with subprocess.Popen(command, cwd=project, env=env, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, start_new_session=True) as child:
        try:
            stdout, _ = child.communicate(timeout=TIMEOUT)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            stdout, _ = child.communicate()
            return subprocess.CompletedProcess(command, 124, stdout)
        return subprocess.CompletedProcess(command, child.returncode, stdout)


def warm(path, key, project, target_file, log, run=native_run):
    roots = read_targets(target_file, key)
    initial_lock = pinned.identity(project)
    repos = [p for p in pinned.lock(project) if p['name'] == 'mathlib']
    if len(repos) != 1 or repos[0]['url'].removesuffix('.git') != 'https://github.com/' + CANONICAL:
        raise ValueError('Warm only the canonical locked Mathlib repository')

    # Download to fresh staging. A partial get- never leaves loadable
    # entries in the eventual cache path.
    remove_entry(path)
    with tempfile.TemporaryDirectory(prefix='inventory-mathlib-native-', dir=path.parent) as tmp:
        staging = Path(tmp) / 'archives'
        staging.mkdir()
        env = {k: v for k, v in pinned.git_env().items()
               if not k.startswith('MATHLIB_CACHE_') and k not in {'LEAN_PATH', 'LEAN_SRC_PATH'}}
        env['MATHLIB_CACHE_DIR'] = str(staging)
        command = ['lake', 'exe', 'cache', 'get-', '--repo=' + CANONICAL, '--cache-from=master', *roots]
        result = run(command, project, env)
        log.parent.mkdir(parents=True, exist_ok=True)
        log.write_bytes(result.stdout)
        if result.returncode or NATIVE_ALL not in result.stdout.decode(errors='replace').splitlines():
            raise ValueError('Pinned Mathlib get- did not confirm a complete upstream download')
        if pinned.identity(project) != initial_lock:
            raise ValueError('Lock inputs changed during upstream download')
        files = archives(staging, with_catalog=False)
        (staging / CATALOG).write_text(json.dumps(describe(key, files), sort_keys=True) + '\n')
        staging.rename(path)
    return {'status': 'ready', 'targets': len(roots), **metrics(files)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['prepare', 'restore', 'warm'])
    parser.add_argument('--cache-key', required=True)
    parser.add_argument('--cache-hit', default='')
    parser.add_argument('--targets-file', type=Path)
    parser.add_argument('--project', type=Path)
    args = parser.parse_args()
    key_target_sha(args.cache_key)
    path = cache_path(Path(os.environ['RUNNER_TEMP']))
    receipt_dir = Path(os.environ['GITHUB_WORKSPACE']) / 'build' / 'dependency-setup'
    start = time.monotonic()
    if args.mode == 'prepare':
        remove_entry(path)
        return
    try:
        if args.mode == 'restore':
            result = use_restore(path, args.cache_key, args.cache_hit)
        else:
            if args.project is None or args.targets_file is None:
                raise ValueError('Warm mode requires project and targets-file')
            result = warm(path, args.cache_key, args.project, args.targets_file,
                          receipt_dir / 'inventory-mathlib-native.log')
    except (ValueError, OSError, RecursionError) as error:
        result = {'status': 'unavailable', 'reason': str(error)}
        try:
            remove_entry(path)
        except OSError as cleanup_error:
            # Status remains unavailable. The caller never consumes this path.
            result['cleanup_error'] = str(cleanup_error)
    receipt = {**result, 'mode': args.mode, 'cache_key': args.cache_key,
               'elapsed_seconds': round(time.monotonic() - start, 3), 'proof_check_run': False}
    receipt_dir.mkdir(parents=True, exist_ok=True)
    (receipt_dir / ('inventory-mathlib-' + args.mode + '.json')).write_text(
        json.dumps(receipt, sort_keys=True, indent=2) + '\n')
    print(json.dumps(receipt, sort_keys=True))
    with Path(os.environ['GITHUB_OUTPUT']).open('a') as out:
        out.write('status=' + result['status'] + '\n')


if __name__ == '__main__':
    main()
