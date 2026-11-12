#!/usr/bin/env python3
"""Run native Windows clean progress cohorts, recursive audit and active packets."""
import concurrent.futures
import hashlib
import json
import os
import platform
from pathlib import Path
import subprocess
import sys
import threading
import time
import traceback
import uuid

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / 'quartics/quartic-318-326/proof/progress'
WORKER = ROOT / 'scripts/windows_audit_worker.py'
PACKETS = ROOT / 'quartics/quartic-318-326/proof/experiments/packets.json'

def installed_toolchain_bin(project, elan_home):
    """Resolve the pinned installed Lean directly without invoking elan."""
    pinned = (project / 'lean-toolchain').read_text(encoding='utf-8').strip()
    if pinned != 'leanprover/lean4:v4.35.0':
        raise RuntimeError('Unexpected pinned toolchain: ' + pinned)
    toolchain_bin = elan_home / 'toolchains' / pinned.replace('/', '--').replace(':', '---') / 'bin'
    if not (toolchain_bin / 'lean.exe').is_file():
        raise RuntimeError('Pinned Lean is not installed at ' + str(toolchain_bin) + '; install it before auditing')
    return toolchain_bin

def main():
    if sys.platform != 'win32' or platform.machine().lower() not in {'amd64', 'x86_64'} or sys.maxsize <= 2**32:
        raise RuntimeError('This adapter requires native x86-64 Windows and 64-bit Python')
    os.environ['PYTHONUTF8'] = '1'
    env = os.environ.copy()
    # Resolve the installed toolchain directly, never through an auto-installing shim.
    # Elan's toolchain directory names escape '/' as '--' and ':' as '---'.
    elan_home = Path(os.environ.get('ELAN_HOME') or Path.home() / '.elan')
    toolchain_bin = installed_toolchain_bin(PROJECT, elan_home).resolve()
    env['QUARTIC_WINDOWS_LEAN_EXE'] = str(toolchain_bin / 'lean.exe')
    env['PATH'] = str(toolchain_bin) + os.pathsep + env['PATH']
    os.environ['PATH'] = env['PATH']  # Windows executable lookup uses parent PATH.
    # Prevent unrelated inherited Lean library paths supplying unchecked imports.
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    run_dir = ROOT / 'audit-results' / ('windows-' + time.strftime('%Y%m%dT%H%M%SZ', time.gmtime()) + '-' + uuid.uuid4().hex[:8])
    run_dir.mkdir(parents=True, exist_ok=False)
    lock = threading.RLock()
    summary = {'status': 'RUNNING', 'stages': {}, 'packets': {},
               'logical_processors': os.cpu_count() or 1,
               'upstream_trust': 'Downloaded upstream artifacts reused; not independently rebuilt.',
               'full_arithmetic_theorem_proved': False}
    def save():
        with lock:
            tmp = run_dir / 'summary.tmp'
            tmp.write_text(json.dumps(summary, indent=2) + '\n', encoding='utf-8')
            tmp.replace(run_dir / 'summary.json')
    def execute(label, args, cwd=PROJECT):
        start = time.monotonic()
        with (run_dir / (label + '.log')).open('w', encoding='utf-8') as log:
            log.write('COMMAND: ' + repr([str(x) for x in args]) + '\n'); log.flush()
            code = subprocess.run([str(x) for x in args], cwd=cwd, env=env,
                                  stdout=log, stderr=subprocess.STDOUT).returncode
        with lock:
            summary['stages'][label] = {'exit_code': code, 'seconds': round(time.monotonic() - start, 2)}
            save()
        print(label, 'exit', code, flush=True)
        return code
    try:
        save(); print('Audit output:', run_dir, flush=True)
        summary['head'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, env=env, text=True).strip()
        # Do not silently check a mixture of tracked working-tree edits and HEAD.
        subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--'], cwd=ROOT, env=env, check=True)
        names = json.loads(PACKETS.read_text(encoding='utf-8'))['active_packets']
        if not names or len(names) != len(set(names)):
            raise ValueError('Invalid active packet list')
        summary['active_packets'] = names
        packet_paths = [PACKETS] + [PACKETS.parent / n / 'intake.json' for n in names]
        packet_hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in packet_paths}
        summary['packet_hashes'] = packet_hashes; save()
        baseline = [sys.executable, '-B', WORKER, 'baseline']
        experiment = [sys.executable, '-B', WORKER, 'experiment']
        common = ['--cohorts', str(os.cpu_count() or 1), '--early-depth', '7', '--split-depth', '16']
        plan = run_dir / 'plan.json'
        if execute('baseline-plan', baseline + ['plan', *common, '--output', plan]):
            raise RuntimeError('Baseline source preflight failed')
        if execute('packet-plan', experiment + ['plan']):
            raise RuntimeError('Packet source preflight failed')
        data = json.loads(plan.read_text(encoding='utf-8'))
        bundles = run_dir / 'bundles'; bundles.mkdir()
        def build(cohort):
            ident = str(cohort['id'])
            return execute('cohort-' + ident, baseline + ['build', *common, '--cohort', ident,
                '--clean', '--bundles', bundles, '--cache', run_dir / ('cache-' + ident),
                '--output', bundles / ('progress-cohort-' + ident)])
        for stage in sorted({c['stage'] for c in data['cohorts']}):
            group = [c for c in data['cohorts'] if c['stage'] == stage]
            with concurrent.futures.ThreadPoolExecutor(max_workers=os.cpu_count() or 1) as pool:
                codes = list(pool.map(build, group))
            if any(codes):
                raise RuntimeError('Cohort stage ' + str(stage) + ' failed; dependent stages blocked')
        full = run_dir / 'baseline-cache'
        if execute('baseline-audit', baseline + ['audit', *common, '--clean', '--bundles', bundles,
                   '--cache', full, '--output', run_dir / 'baseline-audit']):
            raise RuntimeError('Baseline recursive axiom audit failed; packets blocked')
        def packet(name):
            code = execute('packet-' + name, experiment + ['check', '--packet', name,
                '--cache', full, '--output', run_dir / ('packet-output-' + name), '--seconds', '600'])
            with lock:
                summary['packets'][name] = code; save()
            return code
        with concurrent.futures.ThreadPoolExecutor(max_workers=os.cpu_count() or 1) as pool:
            codes = list(pool.map(packet, names))
        if any(codes):
            raise RuntimeError('One or more packet checks failed')
        final_head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, env=env, text=True).strip()
        if final_head != summary['head']:
            raise RuntimeError('Checkout HEAD changed during the audit')
        subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--'], cwd=ROOT, env=env, check=True)
        if any(hashlib.sha256(p.read_bytes()).hexdigest() != packet_hashes[str(p.relative_to(ROOT))] for p in packet_paths):
            raise RuntimeError('Active packet manifest or intake changed during the audit')
        summary['status'] = 'PASS'
    except BaseException as exc:
        summary['status'] = 'FAILED'; summary['error'] = repr(exc)
        (run_dir / 'exception.log').write_text(traceback.format_exc(), encoding='utf-8')
    finally:
        summary['finished_at'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
        save(); print('Summary:', run_dir / 'summary.json', summary['status'], flush=True)
    return 0 if summary['status'] == 'PASS' else 1

if __name__ == '__main__':
    sys.exit(main())
