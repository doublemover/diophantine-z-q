#!/usr/bin/env python3
"""Opt-in Lean pre-commit: check exact staged standalone packets, never install."""
import argparse
from collections import defaultdict
from hashlib import sha256
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time

PROOF = 'quartics/quartic-318-326/proof/'
INTAKE = PROOF + 'intake/'
PROGRESS = PROOF + 'progress/'
PIN = 'leanprover/lean4:v4.35.0'
REV = 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc'
TOOL = 'ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c'
LOCKS = {
    'lean/lean-toolchain': TOOL,
    PROGRESS + 'lean-toolchain': TOOL,
    PROGRESS + 'lakefile.toml': '908476df02b96238ec75ab9f7c953d7d5238b023b87e29a775709d4a62dc2d2a',
    PROGRESS + 'lake-manifest.json': 'a770787f33b5824f61a0731d59e67fca3f44a531b21d1fc1a804064c6fb54e58',
}
FLAGS = ('-j1', '-M', '6144', '-Ddebug.skipKernelTC=false', '-DwarningAsError=true',
         '-Dlinter.unusedSectionVars=true')
PACKET = re.compile(re.escape(INTAKE) + r'([a-z][a-z0-9-]*)/(intake\.json|[A-Za-z_]\w*\.lean)$', re.ASCII)
CONTRACT = re.compile(r'docs/ci-[a-z0-9-]+/CONTRACT\.json$', re.ASCII)
MODULE = re.compile(r'[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*$', re.ASCII)
SIMPLE = re.compile(r'[A-Za-z_]\w*$', re.ASCII)
HEX = re.compile(r'[0-9a-f]{64}$')
CACHE_EXT = ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir', '.ir.sig')
ENV_DROP = ('LEAN_', 'LAKE_', 'ELAN_', 'LD_', 'DYLD_')
GIT_ENV = os.environ | {'GIT_NO_LAZY_FETCH': '1', 'GIT_NO_REPLACE_OBJECTS': '1',
                         'GIT_TERMINAL_PROMPT': '0', 'GIT_OPTIONAL_LOCKS': '0'}


class Blocked(Exception):
    """Cannot validate the requested scope or environment; never a pass."""


class LeanFailure(Exception):
    """The exact pinned compiler rejected staged source."""


def need(condition, message):
    if not condition:
        raise Blocked(message)


def digest(data):
    return sha256(data).hexdigest()


def json_bytes(data):
    return json.dumps(data, sort_keys=True, separators=(',', ':')).encode('ascii')


def json_load(raw):
    def pairs(rows):
        out = {}
        for k, v in rows:
            need(k not in out, 'duplicate JSON key: ' + k)
            out[k] = v
        return out
    return json.loads(raw, object_pairs_hook=pairs)


def safe_path(path):
    need(isinstance(path, str) and re.fullmatch(r'[A-Za-z0-9._/-]+', path)
         and not path.startswith('/') and not ({'.', '..'} & set(path.split('/')))
         and all(path.split('/')), 'noncanonical path: ' + repr(path))
    return path


def git(root, *args):
    try:
        return subprocess.check_output(['git', '--literal-pathspecs', '-C', str(root), *args],
                                       env=GIT_ENV, stderr=subprocess.PIPE, timeout=20)
    except subprocess.CalledProcessError as err:
        raise Blocked('Git index read: ' + err.stderr.decode('utf-8', 'replace').strip()) from err


class Staging:
    def __init__(self, root):
        self.root = root
        self.names = self.changes()
        self.used = {}

    def changes(self):
        return tuple(sorted(x.decode('utf-8') for x in
            git(self.root, 'diff', '--cached', '--name-only', '-z', '--no-renames', '--').split(b'\0') if x))

    def entries(self, paths):
        paths = set(paths)
        if not paths:
            return {}
        for p in paths:
            safe_path(p)
        data = {}
        records = git(self.root, 'ls-files', '--stage', '-z', '--', *sorted(paths)).split(b'\0')
        for rec in filter(None, records):
            fields, raw_name = rec.split(b'\t', 1)
            name = raw_name.decode('utf-8')
            mode, oid, stage = fields.decode('ascii').split()
            need(name in paths and name not in data and mode in ('100644', '100755') and stage == '0',
                 'index content must be a regular, unique stage-zero file: ' + name)
            data[name] = (mode, oid)
        need(set(data) == paths, 'missing staged paths (absent or deleted): ' + ', '.join(sorted(paths-set(data))))
        return data

    def remember(self, paths):
        self.used.update(self.entries(set(paths)-self.used.keys()))

    def read(self, path):
        self.remember([path])
        return git(self.root, 'cat-file', 'blob', self.used[path][1])

    def unchanged(self):
        need(self.changes() == self.names and self.entries(self.used) == self.used,
             'index changed during the lint; run against one fresh staged snapshot')


def code_only(text):
    """Blank strings, nested comments and line comments while preserving newlines."""
    r = list(text)
    i = depth = 0
    quote = False
    while i < len(text):
        two = text[i:i+2]
        if not quote and two in ('/-', '-/') and (two == '/-' or depth):
            depth += 1 if two == '/-' else -1
            r[i:i+2] = '  '
            i += 2
            continue
        if depth:
            if text[i] != '\n':
                r[i] = ' '
        elif quote:
            if text[i] == '"':
                quote = False
            if text[i] == '\\' and i+1 < len(text):
                r[i:i+2] = '  '
                i += 2
                continue
            if text[i] != '\n':
                r[i] = ' '
        elif two == '--':
            end = text.find('\n', i)
            if end < 0:
                end = len(text)
            r[i:end] = ' ' * (end-i)
            i = end
            continue
        elif text[i] == '"':
            quote = True
            r[i] = ' '
        i += 1
    need(not depth and not quote, 'unclosed comment or string: unsupported source input')
    return ''.join(r)


def imports_from_blob(raw):
    code = code_only(raw.decode('utf-8'))
    need(not re.search(
         r'\bset_option\s+(?:linter\s*\.\s*unusedSectionVars|warningAsError|debug\s*\.\s*skipKernelTC|linter\s*\.\s*all)\b',
         code), 'source overrides a required checker option')
    imports = set()
    for line in code.splitlines():
        line = line.strip()
        if not line or line in ('module', 'prelude'):
            continue
        if not re.match(r'^(?:(?:public|meta)\s+)*import\b', line):
            break
        m = re.fullmatch(r'(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*)',
                         line, re.ASCII)
        need(m, 'first release requires one unambiguous import per line: ' + line)
        imports.add(m.group(1))
    return imports


def is_config(path):
    return (path in LOCKS or path.startswith(('lean/', PROGRESS)) and
            PurePosixPath(path).name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'lakefile.lean'))


def get_plans(index, explicit):
    groups = defaultdict(set)
    for p in index.names:
        if is_config(p):
            raise Blocked('staged toolchain/Lake inputs changed; this version validates only the exact current pin')
        m = PACKET.fullmatch(p)
        if m:
            groups[m[1]].add(m[2])
        elif p.endswith('.lean'):
            raise Blocked('outside standalone intake scope: ' + p)
    if not groups:
        need(not any(CONTRACT.fullmatch(p) for p in index.names),
             'contract-only change not supported by the first release')
        return {}
    contracts = sorted({p for p in index.names if CONTRACT.fullmatch(p)} | set(explicit))
    index.remember(set(LOCKS) | set(contracts) | {INTAKE+s+'/intake.json' for s in groups})
    for p, k in LOCKS.items():
        need(digest(index.read(p)) == k, 'staged toolchain/Lake inputs do not equal the supported pin: ' + p)
    mapped = {}
    for p in contracts:
        need(CONTRACT.fullmatch(p), 'not a standalone CI contract path: ' + p)
        rows = json_load(index.read(p))['rows']
        for slug in set(groups) & rows.keys():
            row = rows[slug]
            source_paths = row.get('source_paths', {})
            need(slug not in mapped or mapped[slug] == row, 'conflicting staged intake contracts')
            need(isinstance(source_paths, dict), 'invalid staged donor map')
            mapped[slug] = row

    plans = {}
    for slug, touch in sorted(groups.items()):
        base = INTAKE + slug + '/'
        manifest_raw = index.read(base + 'intake.json')
        mf = json_load(manifest_raw)
        order = mf['order']
        contract = mapped.get(slug)
        if contract is not None:
            need(contract['manifest_sha256'] == digest(manifest_raw),
                 'intake manifest differs from exact staged contract: ' + slug)
        need(isinstance(order, list) and order and all(isinstance(n, str) and SIMPLE.fullmatch(n)
             and n not in ('Lean', 'Init', 'Std', 'Mathlib') for n in order)
             and len(order) == len({n.casefold() for n in order}), 'invalid standalone module order: ' + slug)
        names = {n + '.lean' for n in order}
        need(set(mf['files']) == names and touch <= names | {'intake.json'},
             'manifest file names do not match staged source: ' + slug)
        donor = contract.get('source_paths', {}) if contract else {}
        need(isinstance(donor, dict) and set(donor) <= set(order),
             'staged source map mentions a different packet module: ' + slug)
        paths = {n:safe_path(donor.get(n, base + n + '.lean')) for n in order}
        index.remember(paths.values())
        modules = {}
        for n in order:
            p = paths[n]
            need(PurePosixPath(p).name == n + '.lean' and p.startswith(PROOF),
                 'standalone donor is not the same module in the proof tree: ' + p)
            need(n + '.lean' not in touch or p == base + n + '.lean',
                 'staged local changes would be shadowed by a donor: ' + p)
            raw = index.read(p)
            row = mf['files'][n + '.lean']
            want = row['imports']
            need(digest(raw) == row['sha256'], 'staged source/manifest SHA-256 mismatch: ' + p)
            real = imports_from_blob(raw)
            need(isinstance(want, list) and all(isinstance(x, str) and MODULE.fullmatch(x) for x in want)
                 and len(set(want)) == len(want) and set(want) == real, 'staged imports mismatch: ' + p)
            need(all(dep in modules for dep in real & set(order)), 'nonpreceding packet import: ' + p)
            modules[n] = (p, raw, real)
        # A manifest-only change does not escape elaboration.
        changed = {p.removesuffix('.lean') for p in touch if p != 'intake.json'} or set(order)
        descendants = set(changed)
        for n, (_, _, imps) in modules.items():
            if imps & descendants:
                descendants.add(n)
        active = set(descendants)
        for n in reversed(order):
            if n in active:
                active |= modules[n][2] & modules.keys()
        plans[slug] = (modules, descendants, active)
    return plans


def sanitized_env():
    return {k: v for k, v in os.environ.items() if not k.startswith(ENV_DROP)}


def verified_compiler(path, env):
    need(path is not None, 'set QUARTIC_LEAN to an already installed official Lean binary; no install is attempted')
    passed = Path(path).expanduser().absolute()
    exe = passed.resolve()
    need(exe.is_file() and exe.name.lower() in ('lean','lean.exe') and
         not (passed.parent.name == 'bin' and passed.parent.parent.name == '.elan'),
         'use the real pinned toolchain binary, not an elan shim')
    v = subprocess.check_output([str(exe), '--version'], env=env, timeout=5, text=True).strip()
    need(re.fullmatch(r'Lean \(version 4\.35\.0, [^,]+, commit ' + REV + r', Release\)', v),
         'wrong Lean compiler: ' + v)
    identity = digest(json_bytes({'pin': PIN, 'version': v, 'system': platform.system(),
                                  'machine': platform.machine(), 'locks': LOCKS, 'flags': FLAGS,
                                  'implementation': digest(Path(__file__).read_bytes())}))
    return exe, identity, v


def regular(root, path):
    p = root / safe_path(path)
    need(p.is_file() and p.resolve() == p, 'missing or redirected file: ' + str(p))
    return p


def upstream(args, core, roots):
    if not roots:
        return (), 'builtin'
    need(args.upstream and args.upstream_sha and HEX.fullmatch(args.upstream_sha),
         'pinned upstream imports missing; set QUARTIC_LEAN_UPSTREAM and QUARTIC_LEAN_UPSTREAM_SHA256')
    root = Path(args.upstream).resolve()
    raw = regular(root, 'upstream.json').read_bytes()
    need(digest(raw) == args.upstream_sha, 'upstream cache manifest SHA-256 mismatch')
    spec = json_load(raw)
    need(spec['version'] == 1 and spec['environment'] == core and roots <= set(spec['roots']),
         'upstream compiler/lock/platform or required roots differ')
    names = set(spec['files'])
    libraries = tuple(root / safe_path(p) for p in spec['libraries'])
    need(libraries and len(libraries) == len(set(libraries))
         and all(p.is_dir() and p.resolve() == p for p in libraries), 'invalid upstream library directories')
    current = set()
    for lib in libraries:
        for p in lib.rglob('*'):
            need(not p.is_symlink() and (p.is_dir() or p.is_file()), 'redirected upstream tree: ' + str(p))
            if p.is_file():
                rel = p.relative_to(lib)
                first = rel.parts[0].split('.',1)[0]
                need(first not in ('Lean','Init','Std') and
                     (p.name.endswith(CACHE_EXT) or p.suffix in ('.so','.dll','.dylib')),
                     'unexpected file or builtin namespace shadow in upstream bundle: ' + str(rel))
                current.add(p.relative_to(root).as_posix())
    need(current == names, 'upstream artifact content inventory differs')
    for p in sorted(names):
        need(digest(regular(root, p).read_bytes()) == spec['files'][p], 'changed upstream cache entry: ' + p)
    need(all(sum((lib / (n.replace('.', '/') + '.olean')).exists() for lib in libraries) == 1
             for n in roots), 'missing or ambiguous direct artifact in verified upstream cache')
    return libraries, args.upstream_sha


def restore(cache, key, n, output):
    if not cache:
        return False
    root = cache / key
    if not root.exists():
        return False
    need(root.resolve() == root and root.is_dir(), 'redirected dependency cache entry')
    files = json_load(regular(root, 'entry.json').read_bytes())
    need(files['key'] == key and files['module'] == n, 'foreign dependency cache entry')
    payload = files['files']
    safe = {n + ext for ext in CACHE_EXT}
    need(n+'.olean' in payload and set(payload) <= safe and
         {p.name for p in root.iterdir()} == set(payload) | {'entry.json'}, 'unexpected dependency cache contents')
    for f, h in payload.items():
        b = regular(root, f).read_bytes()
        need(digest(b) == h, 'corrupt dependency cache data: ' + n)
        (output / f).write_bytes(b)
    return True


def store_module(cache, key, n, output):
    if not cache:
        return
    with tempfile.TemporaryDirectory(prefix='pending-', dir=cache) as t:
        directory = Path(t) / 'object'
        directory.mkdir()
        data = {}
        for ext in CACHE_EXT:
            p = output / (n + ext)
            if p.is_file():
                b = p.read_bytes()
                (directory / p.name).write_bytes(b)
                data[p.name] = digest(b)
        need(n + '.olean' in data, 'compiler did not produce required artifact for ' + n)
        (directory/'entry.json').write_bytes(json_bytes(dict(key=key,module=n,files=data)))
        dest = cache / key
        try:
            directory.rename(dest)
        except OSError:
            if not dest.is_dir():
                raise
            # Another process may have checked the same immutable dependency.
            check = Path(t)/'verify'; check.mkdir()
            need(restore(cache, key, n, check), 'concurrent dependency object missing')
            # On failures, never admit unvalidated stale bytes.


def run_plan(exe, plans, env, libraries, identity, cache, deadline, stats):
    for slug, (modules, targets, active) in plans.items():
        with tempfile.TemporaryDirectory(prefix='quartic-staged-lean-') as t:
            source = Path(t)/'source'; source.mkdir()
            output = Path(t)/'lib'; output.mkdir()
            local_env = env | {'LEAN_PATH':os.pathsep.join(map(str, (output,*libraries)))}
            keys = {}
            for n, (p, raw, imps) in modules.items():
                if n not in active:
                    continue
                keys[n] = digest(json_bytes({'environment': identity, 'module': n, 'source':digest(raw),
                                           'imports': [[dep,keys.get(dep,'immutable-system')]
                                                       for dep in sorted(imps)]}))
                now = time.perf_counter()
                hit = n not in targets and restore(cache, keys[n], n, output)
                stats['module_cache_seconds'] += time.perf_counter()-now
                if hit:
                    stats['reused'].append(n)
                    continue
                src = source/(n+'.lean')
                src.write_bytes(raw)
                remain = deadline - time.perf_counter()
                need(remain > 0, 'lint budget exhausted; no result')
                now = time.perf_counter()
                try:
                    r = subprocess.run([str(exe), *FLAGS, '--json', '-R', str(source),
                        '-o', str(output/(n+'.olean')), str(src)], cwd=source, env=local_env,
                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=remain)
                finally:
                    elapsed = time.perf_counter()-now
                    stats['target_lean_seconds' if n in targets else 'dependency_lean_seconds'] += elapsed
                msg = r.stdout.replace(str(src), p)
                if r.returncode:
                    if re.search(r'object file .* does not exist|unknown module prefix|invalid import|incompatible.*olean',
                                 msg, re.IGNORECASE):
                        raise Blocked(f'{p}: missing or incompatible Lean imports\n{msg.rstrip()}')
                    raise LeanFailure(f'{p}: Lean exit {r.returncode}\n{msg.rstrip()}')
                stats['elaborated'].append(n)
                need((output/(n+'.olean')).is_file(), 'compiler produced no expected module artifact')
                # Never cache the checked target itself as a substitute for its next lint.
                if n not in targets:
                    now = time.perf_counter()
                    store_module(cache, keys[n], n, output)
                    stats['module_cache_seconds'] += time.perf_counter()-now


def cli(args, stats, start):
    root = Path(git(Path.cwd(),'rev-parse','--show-toplevel').decode().strip()).resolve()
    index = Staging(root)
    plans = get_plans(index,args.contract)
    stats['index_seconds'] = time.perf_counter()-start
    if not plans:
        return 'N/A'
    now = time.perf_counter()
    env = sanitized_env()
    exe, core, version = verified_compiler(args.lean,env)
    stats['compiler'] = version
    stats['environment'] = core
    stats['compiler_seconds'] = time.perf_counter()-now
    choices = [d for mods, _, active in plans.values() for n, (_, _, imps) in mods.items()
               if n in active for d in imps if d not in mods and d.split('.',1)[0] not in ('Init','Lean','Std')]
    now = time.perf_counter()
    libs, up = upstream(args,core,set(choices))
    stats['upstream_validation_seconds'] = time.perf_counter()-now
    cache = Path(args.cache).expanduser().resolve() if args.cache else None
    if cache:
        cache.mkdir(parents=True,exist_ok=True)
    run_plan(exe,plans,env,libs,digest(json_bytes([core,up])),cache,start+args.budget,stats)
    index.unchanged()
    need(time.perf_counter() <= start+args.budget, 'lint budget exceeded; no result')
    return 'PASS'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean',default=os.getenv('QUARTIC_LEAN'))
    parser.add_argument('--cache',default=os.getenv('QUARTIC_LEAN_MODULE_CACHE'))
    parser.add_argument('--upstream',default=os.getenv('QUARTIC_LEAN_UPSTREAM'))
    parser.add_argument('--upstream-sha',default=os.getenv('QUARTIC_LEAN_UPSTREAM_SHA256'))
    parser.add_argument('--contract',action='append',default=[])
    parser.add_argument('--budget',type=float,default=20)
    args = parser.parse_args()
    stats = dict(elaborated=[],reused=[],index_seconds=0.,compiler_seconds=0.,
                 upstream_validation_seconds=0.,module_cache_seconds=0.,dependency_lean_seconds=0.,
                 target_lean_seconds=0.)
    start = time.perf_counter()
    try:
        need(0 < args.budget <= 300,'budget must lie in (0, 300] seconds')
        stats['status'] = cli(args,stats,start)
        code = 0
    except LeanFailure as err:
        stats['status'],stats['diagnostic'],code = 'FAIL',str(err),1
    except (Blocked, subprocess.SubprocessError, OSError, KeyError, TypeError, ValueError) as err:
        stats['status'],stats['diagnostic'],code = 'NOT RUN / BLOCKED',str(err),2
    stats['elapsed_seconds'] = time.perf_counter()-start
    if 'diagnostic' in stats:
        print(stats['diagnostic'],file=sys.stderr)
    print(json.dumps(stats))
    return code


if __name__ == '__main__':
    raise SystemExit(main())
