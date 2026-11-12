#!/usr/bin/env python3
"""Hosted-only, non-admitted original/explicit-premise signature diagnostics.

Uses the existing strict packet checker, existing 180-second module cap, and
existing serialized PEL job. It does not infer hidden premises from token use.
"""
import json
import os
import signal
from pathlib import Path
import subprocess
import sys

PACKETS = (
    'pel-original-generic-binder-original-probe-r2',
    'pel-original-generic-binder-included-probe-r2',
)

SLOT_PREFIX = 'pel-original-character-'

def require_unique_slot(packets):
    selected = [name for name in packets if name.startswith(SLOT_PREFIX)]
    if len(selected) != 1:
        raise ValueError('Binder diagnostic requires exactly one active PEL character slot')
    return selected[0]

def main():
    if os.environ.get('GITHUB_ACTIONS') != 'true':
        raise SystemExit('Hosted diagnostic only; do not compile locally.')
    root = Path(__file__).resolve().parents[1]
    registry = root / 'quartics/quartic-318-326/proof/experiments/packets.json'
    require_unique_slot(json.loads(registry.read_text())['active_packets'])
    output = root / 'build/generic-binder-diagnostics'
    output.mkdir(parents=True, exist_ok=True)
    rows = []
    controls = root / 'quartics/quartic-318-326/proof/experiments' / PACKETS[0] / 'diagnostic-controls'
    for name in ('BinderControls318.lean', 'BinderExpectedFailure318.lean'):
        with (output / (name + '.log')).open('w') as log:
            try:
                result = subprocess.run(['lean', str(controls / name)],
                                        stdout=log, stderr=subprocess.STDOUT,
                                        timeout=180, check=False)
                rows.append({'control': name, 'exit_code': result.returncode,
                             'expected_failure': name == 'BinderExpectedFailure318.lean'})
            except subprocess.TimeoutExpired:
                rows.append({'control': name, 'status': 'CONTROL_LIMIT_180_SECONDS'})
    for packet in PACKETS:
        command = [sys.executable, '-B', str(root / 'scripts/check_progress_experiment.py'),
                   'check', '--packet', packet, '--cache', str(root / '.cache/progress-ci'),
                   '--output', str(output / packet), '--seconds', '180']
        # Separate processes and directories ensure a failed original cannot
        # suppress or contaminate the explicitly included variant.
        with (output / (packet + '.driver.log')).open('w') as log:
            process = subprocess.Popen(command, start_new_session=True,
                                       stdout=log, stderr=subprocess.STDOUT)
            try:
                code = process.wait(timeout=600)
                rows.append({'packet': packet, 'exit_code': code})
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                rows.append({'packet': packet, 'status': 'DIAGNOSTIC_TOTAL_LIMIT_600_SECONDS'})
    (output / 'SUMMARY.json').write_text(json.dumps({
        'scope': 'Signature evidence or exact first blocking error, not production admission.',
        'source_syntax_vs_elaborated_type_automatic_matcher_implemented': False,
        'packets': rows,
    }, indent=2) + '\n')

if __name__ == '__main__':
    main()
