#!/usr/bin/env python3
"""Hosted-only no-sorry isolated original/candidate diagonal profiling.

Separate from the original r26 scratch bisection. No olean, cache, admission,
production-source mutation, or proof-acceptance receipt is produced.
"""
import argparse
import hashlib
import json
import os
import selectors
import subprocess
import time
from pathlib import Path
import tempfile
import diagnose_original_endpoint as original

ci = original.ci
PACKET = 'contact-relative-site-descent-r30'
CONTROL_PACKET = 'contact-relative-site-descent-r29'
CONTROL_SHA = '13aa4e158e55d9e638bb7e9495c1f605417077ae5698c689764b3d8935366bb8'
SOURCE_SHA = 'a2baa89e3af5ee53525c269bea597535da4e0999f0b95db6e5042ae11e0b29e8'


def variants(source, control):
    def prefix(text):
        return text[:text.index('\nvariable (R S')] + '\nend OriginalGeometricDiagonal318\n'
    control = control.replace('universe u\n',
        'universe u\nset_option stderrAsMessages false\n', 1)
    for name in ('split_sections', 'diagonal_to_split'):
        control = control.replace('lemma '+name,
            'set_option profiler true in\nset_option profiler.threshold 0 in\nlemma '+name, 1)
    def controls(text):
        for name in ('split_sections', 'diagonal_to_split'):
            scope = 'set_option profiler true in\nset_option profiler.threshold 0 in\nlemma '+name
            positive = ('set_option profiler true in\nset_option profiler.threshold 0 in\n'
                'private theorem diagnostic_positive_'+name+' : True := True.intro\n'
                'run_cmd do\n  let e ← IO.getStderr\n'
                '  e.putStrLn "DIAGONAL positive control before '+name+'"\n  e.flush\n\n')
            assert scope in text
            text = text.replace(scope, positive+scope, 1)
        return text
    control, source = controls(control), controls(source)
    result = {'original_split_prefix':prefix(control), 'original_full':control,
              'named_identity_split_prefix':prefix(source), 'named_identity_full':source}
    assert all('sorry' not in text for text in result.values())
    return result


def parse_memory_status(text):
    names = {'VmRSS:': 'peak_rss_kib', 'VmHWM:': 'peak_hwm_kib'}
    result = {}
    for line in text.splitlines():
        fields = line.split()
        if len(fields) == 3 and fields[0] in names and fields[2] == 'kB':
            result[names[fields[0]]] = int(fields[1])
    return result


def bounded_memory(source, root, env, log):
    command = ['lean', *ci.FLAGS, '-R', str(root), str(source)]
    start = time.monotonic()
    process = subprocess.Popen(command, cwd=ci.PROJECT, env=env,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    selector = selectors.DefaultSelector()
    selector.register(process.stdout, selectors.EVENT_READ)
    memory = {'sample_count': 0, 'peak_rss_kib': None, 'peak_hwm_kib': None}
    def sample():
        try:
            values = parse_memory_status(Path(f'/proc/{process.pid}/status').read_text())
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            return
        memory['sample_count'] += 1
        for key, value in values.items():
            memory[key] = max(memory[key] or 0, value)
    size = 0
    stopped = None
    with log.open('wb') as stream:
        while selector.get_map():
            sample()
            if time.monotonic() - start > original.SECONDS:
                stopped = 'SCRATCH_WALL_LIMIT'
                process.kill()
                break
            events = selector.select(timeout=0.2)
            sample()
            for key, _ in events:
                chunk = os.read(key.fileobj.fileno(), 65536)
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                remaining = original.MAX_BYTES - size
                stream.write(chunk[:remaining])
                size += min(len(chunk), remaining)
                if len(chunk) > remaining:
                    stopped = 'SCRATCH_LOG_LIMIT'
                    process.kill()
                    break
            if stopped:
                break
        process.wait(timeout=10)
        if stopped:
            stream.write(('\n' + stopped + '\n').encode())
    selector.close()
    process.stdout.close()
    return {'variant': source.stem, 'exit_code': process.returncode,
        'seconds': round(time.monotonic()-start, 3), 'bytes': size,
        'limit': stopped, 'admitted': False, 'proof_acceptance': False,
        'memory': memory, 'memory_scope': 'sampled /proc of spawned Lean PID; not descendants',
        'memory_sample_interval_target_seconds': 0.2}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--packet', required=True, choices=[PACKET])
    args = parser.parse_args()
    if os.environ.get('GITHUB_ACTIONS') != 'true' or not os.environ.get('RUNNER_TEMP'):
        raise RuntimeError('This diagnostic may run only on hosted GitHub Actions')
    output = ci.ROOT/'build/progress-experiments'/args.packet
    lib = output/'lib'
    if not all((lib/(n+'.olean')).is_file() for n in
               ('OriginalGeometricTriple318','AffineOverlapDiagonal318')):
        raise RuntimeError('Required normally compiled predecessor is unavailable')
    path = ci.ROOT/'quartics/quartic-318-326/proof/experiments'/args.packet/'OriginalGeometricDiagonal318.lean'
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SOURCE_SHA:
        raise RuntimeError('Candidate source changed from independently reviewed bytes')
    control = (path.parent.parent/CONTROL_PACKET/path.name).read_bytes()
    if hashlib.sha256(control).hexdigest() != CONTROL_SHA:
        raise RuntimeError('Original diagonal control differs from exact hosted bytes')
    env, version = ci.environment(ci.PROJECT, lib)
    logs = output/'scratch-diagonal-identity-diagnostics'
    logs.mkdir(exist_ok=False)
    rows = []
    with tempfile.TemporaryDirectory(prefix='diagonal-identity-nonadmitted-',
                                    dir=os.environ['RUNNER_TEMP']) as directory:
        root = Path(directory)
        for name, text in variants(raw.decode(),control.decode()).items():
            source = root/(name+'.lean')
            source.write_text(text)
            row = bounded_memory(source, root, env, logs/(name+'.log'))
            row['source_sha256'] = hashlib.sha256(text.encode()).hexdigest()
            row['contains_sorry'] = False
            rows.append(row)
            print(json.dumps(row), flush=True)
    ci.write_json(logs/'DIAGNOSTIC.json', {'scope':'NON_ADMITTED_DIAGONAL_IDENTITY_SCRATCH_ONLY',
        'source_sha256':SOURCE_SHA, 'control_sha256':CONTROL_SHA, 'toolchain':version, 'variants':rows,
        'baseline_or_experiment_accepted':False, 'writes_olean':False})


if __name__ == '__main__':
    main()
