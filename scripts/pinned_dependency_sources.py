#!/usr/bin/env python3
"""Verified, lockfile-exact Git source bundles. Never cache/admit Lean artifacts.

A cache is transport only: rebuild fresh Git repositories, verify the locked
commit and every worktree byte, and only then allow Lake to read dependencies.
No lake update, cache-supplied config/index/hooks, or floating revisions.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import signal
import subprocess
import tempfile
import time

ATTEMPTS = 3
ATTEMPT_SECONDS = 180
DELAYS = (5, 15)
TRANSIENT = re.compile(r'(?:requested URL returned error:|HTTP(?:/[0-9.]+)?(?: error)?[: ]+|status code[: ]+)\s*(?:429|500|502|503|504)\b|Could not resolve host|Connection (?:timed out|reset)|Failed to connect|TLS connection was non-properly terminated|curl: \((?:6|7|18|28|35|52|56)\)', re.I)
COMPILE_ERROR = re.compile(r'\.lean:\d+:\d+: (?:error|warning)|error: build failed')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def git_env():
    env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
    env.update(GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull,
               GIT_TERMINAL_PROMPT='0', GIT_NO_REPLACE_OBJECTS='1')
    return env


def git(repo, *args):
    return ['git', '--no-replace-objects', '-c', 'core.hooksPath=/dev/null',
            '-c', 'core.fsmonitor=false', '-c', 'core.autocrlf=false',
            '-c', 'submodule.recurse=false', '-c', 'fetch.fsckObjects=true',
            '-c', 'transfer.fsckObjects=true', '-C', str(repo), *args]


def run(args, timeout=ATTEMPT_SECONDS):
    with subprocess.Popen(args, env=git_env(), stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, start_new_session=True) as p:
        try:
            output, _ = p.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL)
            output, _ = p.communicate()
            raise subprocess.TimeoutExpired(args, timeout, output=output)
        return subprocess.CompletedProcess(args, p.returncode, output)


def checked(args):
    p = run(args)
    if p.returncode:
        raise RuntimeError(p.stdout.decode(errors='replace'))
    return p.stdout


def acquire(args, label, receipt, log, runner=run, sleeper=time.sleep):
    """Retry only transport failures, never integrity checks or proof commands."""
    for attempt in range(1, ATTEMPTS + 1):
        try:
            p = runner(args)
            code, output = p.returncode, p.stdout
        except subprocess.TimeoutExpired as e:
            code, output = 124, (e.stdout or b'') + b'\nACQUISITION_TIMEOUT\n'
        log.parent.mkdir(parents=True, exist_ok=True)
        with log.open('ab') as f:
            f.write(f'\n[{label} attempt {attempt}]\n'.encode() + output)
        text = output.decode(errors='replace')
        print(text, flush=True)
        transient = not COMPILE_ERROR.search(text) and (code == 124 or bool(TRANSIENT.search(text)))
        receipt['attempts'].append(dict(label=label, attempt=attempt, exit_code=code,
                                        output_sha256=digest(output), transient=bool(transient)))
        if code == 0:
            return
        if attempt == ATTEMPTS or not transient:
            raise AcquisitionError(code, label)
        sleeper(DELAYS[attempt - 1])


class AcquisitionError(RuntimeError):
    def __init__(self, code, label):
        self.code = code
        super().__init__(f'{label} acquisition failed, exit {code}')


def lock(project):
    manifest = project / 'lake-manifest.json'
    data = json.loads(manifest.read_text())
    if data.get('packagesDir') != '.lake/packages' or data.get('lakeDir') != '.lake':
        raise ValueError('Unexpected Lake layout')
    names = set()
    for p in data['packages']:
        if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_-]*', p['name']) or p['name'] in names:
            raise ValueError('Unsafe/duplicate package name')
        names.add(p['name'])
        if p.get('type') != 'git' or p.get('subDir') is not None:
            raise ValueError('Only exact root Git packages supported')
        if not re.fullmatch(r'https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?', p['url']):
            raise ValueError('Unexpected package URL')
        if not re.fullmatch('[0-9a-f]{40}', p['rev']):
            raise ValueError('Package revision must be a full commit')
        if p.get('manifestFile') != 'lake-manifest.json' or p.get('configFile') not in ('lakefile.lean', 'lakefile.toml'):
            raise ValueError('Unexpected package configuration path')
    return data['packages']


def identity(project):
    return {name: digest((project / name).read_bytes())
            for name in ('lake-manifest.json', 'lean-toolchain', 'lakefile.toml')} | {
                'protocol': 1, 'helper_sha256': digest(Path(__file__).read_bytes())}


def fresh_repo(path, rev):
    path.mkdir()
    checked(git(path, 'init', '--template='))
    # Bundle protocol intentionally keeps only one pinned source snapshot. Its
    # parents are not needed or trusted. This explicit boundary is NOT cached.
    (path / '.git/shallow').write_text(rev + '\n')


def verify_checkout(path, package):
    rev = package['rev']
    if checked(git(path, 'rev-parse', 'HEAD')).decode().strip() != rev:
        raise ValueError('Wrong package HEAD')
    if checked(git(path, 'remote', 'get-url', 'origin')).decode().strip() != package['url']:
        raise ValueError('Wrong package URL')
    checked(git(path, 'fsck', '--full', '--strict'))
    entries = checked(git(path, 'ls-tree', '-rz', '--full-tree', rev)).split(b'\0')
    expected = set()
    for entry in filter(None, entries):
        info, name = entry.split(b'\t', 1)
        mode, kind, oid = info.decode().split()
        name = name.decode('utf-8')
        parts = PurePosixPath(name).parts
        if not parts or name.startswith('/') or any(x in ('.', '..', '.git', '.lake') for x in parts):
            raise ValueError('Unsafe/generated tree path')
        if mode not in ('100644', '100755', '120000') or kind != 'blob':
            raise ValueError('Submodules/special files are not permitted')
        if name.endswith(('.olean', '.olean.private', '.olean.server', '.ilean', '.ir', '.o', '.so', '.dll', '.dylib', '.a', '.obj', '.exe', '.bc')):
            raise ValueError('Compiled artifact in dependency source tree')
        target = path / name
        # No symlink directory traversal, even when a file's own bytes match.
        if any((path.joinpath(*parts[:i])).is_symlink() for i in range(1, len(parts))):
            raise ValueError('Symlink ancestor')
        if mode == '120000':
            if not target.is_symlink():
                raise ValueError('Symlink mode mismatch')
            raw = os.readlink(target).encode()
            resolved = (target.parent / os.readlink(target)).resolve()
            if not resolved.is_relative_to(path.resolve()) or '.git' in resolved.relative_to(path.resolve()).parts:
                raise ValueError('Escaping symlink')
        else:
            if target.is_symlink() or not target.is_file():
                raise ValueError('File mode mismatch')
            raw = target.read_bytes()
            if bool(target.stat().st_mode & 0o111) != (mode == '100755'):
                raise ValueError('Executable mode mismatch')
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        if blob != oid:
            raise ValueError('Source bytes differ from locked tree')
        expected.add(name)
    actual = set()
    for folder, dirs, files in os.walk(path, followlinks=False):
        if Path(folder) == path:
            dirs.remove('.git')
        for name in dirs[:]:
            q = Path(folder) / name
            if q.is_symlink():
                actual.add(q.relative_to(path).as_posix()); dirs.remove(name)
        for name in files:
            actual.add((Path(folder) / name).relative_to(path).as_posix())
    if actual != expected:
        raise ValueError('Unexpected/untracked or missing dependency files')
    return len(expected)


def sources(project, cache, receipt, log):
    packages = lock(project)
    ident = identity(project)
    cache.parent.mkdir(parents=True, exist_ok=True)
    if cache.is_symlink():
        raise ValueError('Symlink cache root')
    hit = cache.exists() and any(cache.iterdir())
    receipt['cache'] = 'source-hit-validation-pending' if hit else 'source-miss'
    if hit:
        expected = {'identity.json'} | {p['name'] + '.bundle' for p in packages}
        if {p.name for p in cache.iterdir()} != expected or any(p.is_symlink() or not p.is_file() for p in cache.iterdir()):
            raise ValueError('Unexpected cache entries')
        if json.loads((cache / 'identity.json').read_text()) != ident:
            raise ValueError('Cache identity differs from full lock/toolchain/helper')
    else:
        cache.mkdir(exist_ok=True)
    dest = project / '.lake/packages'
    if (project / '.lake').is_symlink() or dest.is_symlink():
        raise ValueError('Unsafe package root')
    dest.mkdir(parents=True, exist_ok=True)
    if any(p.name not in {q['name'] for q in packages} for p in dest.iterdir()):
        raise ValueError('Unexpected existing package destination')
    receipt['packages'] = []
    with tempfile.TemporaryDirectory(prefix='pinned-sources-', dir=project / '.lake') as tmp:
        for p in packages:
            work = Path(tmp) / p['name']
            fresh_repo(work, p['rev'])
            bundle = cache / (p['name'] + '.bundle')
            if hit:
                # Only HEAD is imported; no bundle refs/config/index/hooks.
                checked(git(work, 'fetch', '--no-tags', str(bundle.resolve()), 'HEAD'))
            else:
                acquire(git(work, 'fetch', '--no-tags', '--depth=1', p['url'], p['rev']),
                        p['name'], receipt, log)
            if checked(git(work, 'rev-parse', 'FETCH_HEAD')).decode().strip() != p['rev']:
                raise ValueError('Fetched commit differs from manifest')
            checked(git(work, 'checkout', '--detach', p['rev']))
            checked(git(work, 'remote', 'add', 'origin', p['url']))
            count = verify_checkout(work, p)
            if not hit:
                checked(git(work, 'bundle', 'create', str(bundle.resolve()), 'HEAD'))
            final = dest / p['name']
            # Existing mutable Lake output is not a source of trusted bytes.
            if final.is_symlink():
                raise ValueError('Symlink package destination')
            if final.exists():
                shutil.rmtree(final)
            work.rename(final)
            receipt['packages'].append(dict(name=p['name'], rev=p['rev'], url=p['url'], files=count))
    if identity(project) != ident:
        raise ValueError('Lock inputs changed during setup')
    (cache / 'identity.json').write_text(json.dumps(ident, sort_keys=True) + '\n')
    receipt['cache'] = 'verified-source-hit' if hit else 'source-miss-verified'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['sources', 'artifacts'])
    parser.add_argument('--project', type=Path, required=True)
    parser.add_argument('--cache', type=Path)
    parser.add_argument('--targets-file', type=Path)
    parser.add_argument('--receipt', type=Path, required=True)
    args = parser.parse_args()
    args.receipt = args.receipt.resolve()
    project = args.project.resolve()
    receipt = {'mode': args.mode, 'attempts': [], 'status': 'FAIL', 'proof_check_run': False}
    log = args.receipt.with_suffix('.log')
    code = 1
    try:
        receipt['identity'] = identity(project)
        if args.mode == 'sources':
            if args.cache is None:
                raise ValueError('sources requires cache')
            sources(project, args.cache, receipt, log)
        else:
            if args.targets_file is None:
                raise ValueError('artifacts requires targets-file')
            targets = args.targets_file.read_text().splitlines()
            if not targets or any(not re.fullmatch(r'[A-Za-z0-9_./-]+', t) or t.startswith('-') or '..' in t.split('/') for t in targets):
                raise ValueError('Invalid upstream cache targets')
            before = identity(project)
            os.chdir(project)
            acquire(['lake', 'exe', 'cache', 'get', *targets], 'upstream-artifacts', receipt, log.resolve())
            if identity(project) != before:
                raise ValueError('Lock inputs changed during artifact acquisition')
        receipt['status'] = 'PASS'
        code = 0
    except AcquisitionError as e:
        code = e.code if 0 < e.code < 256 else 1
        receipt['error'] = str(e)
    except Exception as e:
        receipt['error'] = str(e)
    finally:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(receipt, indent=2) + '\n')
    return code


if __name__ == '__main__':
    raise SystemExit(main())
