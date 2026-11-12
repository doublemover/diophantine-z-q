#!/usr/bin/env python3
"""Windows-specific adapter for the repository's existing audit checkers."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

import check_progress_lean as ci

# One Lean worker per process. The orchestrator runs up to one process per
# logical CPU. No explicit Lean memory cap or per-command wall-clock limit.
ci.FLAGS = ['-j1', '-Ddebug.skipKernelTC=false']
# Extend only the local adapter's cohort CLI; hosted defaults remain unchanged.
_original_add_argument = argparse.ArgumentParser.add_argument
def add_argument(parser, *args, **kwargs):
    if '--cohorts' in args:
        kwargs['choices'] = range(1, max(33, (os.cpu_count() or 1) + 1))
    return _original_add_argument(parser, *args, **kwargs)
argparse.ArgumentParser.add_argument = add_argument
_original_digest = ci.digest

def windows_digest(value):
    if isinstance(value, dict) and value.get('platform') == 'linux-x86_64':
        value = {**value, 'platform': 'windows-x86_64',
                 'windows_adapter_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    return _original_digest(value)

ci.digest = windows_digest

# Never download or build in the shared package tree. Imports in downloaded
# upstream oleans remain trusted inputs; Lean reports missing transitive files.
def require_upstream(project, env, logs):
    packages = json.loads((project / 'lake-manifest.json').read_text())['packages']
    libs = [project / '.lake/packages' / p['name'] / '.lake/build/lib/lean' for p in packages]
    local = set(json.loads((project / 'checkpoint-manifest.json').read_text())['module_order'])
    roots = {n.replace('/', '.') for n in ci.OFFICIAL}
    for name in local:
        roots.update(ci.import_names((project / (name.replace('.', '/') + '.lean')).read_text()) - local)
    missing = [n for n in sorted(roots) if n.split('.')[0] not in {'Lean', 'Std', 'Init'}
               and not any((lib / (n.replace('.', '/') + '.olean')).is_file() for lib in libs)]
    if missing:
        raise RuntimeError('Missing upstream artifacts (no download attempted): ' + ', '.join(missing))

ci.ensure_official = require_upstream
_original_run = subprocess.run

def no_timeout(*args, **kwargs):
    if 'timeout' in kwargs:
        kwargs['timeout'] = None
    if args and isinstance(args[0], (list, tuple)) and args[0] and args[0][0] == 'lean':
        executable = os.environ.get('QUARTIC_WINDOWS_LEAN_EXE')
        if not executable or not Path(executable).is_absolute():
            raise RuntimeError('Missing absolute installed Lean executable')
        args = ([executable, *args[0][1:]], *args[1:])
    return _original_run(*args, **kwargs)

subprocess.run = no_timeout
if __name__ == '__main__':
    mode = sys.argv.pop(1)
    if mode == 'baseline':
        ci.main()
    elif mode == 'experiment':
        import check_progress_experiment as experiment
        experiment.main()
    else:
        raise ValueError('Unknown audit worker mode: ' + mode)
