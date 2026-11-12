#!/usr/bin/env python3
"""Pure Python driver controls; does not execute Lean or a subprocess."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
from unittest.mock import Mock, patch
import diagnose_generic_binders as driver

def main():
    registry = Path(__file__).resolve().parents[1] / 'quartics/quartic-318-326/proof/experiments/packets.json'
    driver.require_unique_slot(json.loads(registry.read_text())['active_packets'])
    for invalid in ([], ['pel-original-character-a', 'pel-original-character-b']):
        try:
            driver.require_unique_slot(invalid)
            raise AssertionError('invalid duplicate/missing diagnostic slot accepted')
        except ValueError:
            pass
    with patch.dict(os.environ, {'GITHUB_ACTIONS': 'false'}):
        try:
            driver.main()
            raise AssertionError('local compilation guard missing')
        except SystemExit as e:
            assert 'Hosted diagnostic only' in str(e)
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        registry = root / 'quartics/quartic-318-326/proof/experiments/packets.json'
        registry.parent.mkdir(parents=True)
        registry.write_text(json.dumps({'active_packets': ['pel-original-character-test']}))
        original = Mock(pid=123)
        original.wait.side_effect = [subprocess.TimeoutExpired('checker', 600), -9]
        included = Mock(pid=124)
        included.wait.return_value = 0
        with patch.object(driver, '__file__', str(root / 'scripts/driver.py')), \
             patch.dict(os.environ, {'GITHUB_ACTIONS': 'true'}), \
             patch.object(driver.subprocess, 'run', side_effect=[Mock(returncode=0), Mock(returncode=1), Mock(returncode=1)]) as control, \
             patch.object(driver.subprocess, 'Popen', side_effect=[original, included]) as spawn, \
             patch.object(driver.os, 'killpg') as kill:
            driver.main()
        assert control.call_count == 3
        assert spawn.call_count == 2
        assert all(c.kwargs['start_new_session'] for c in spawn.call_args_list)
        kill.assert_called_once_with(123, driver.signal.SIGKILL)
        assert original.wait.call_count == 2 and included.wait.call_count == 1
        out = root / 'build/generic-binder-diagnostics'
        data = json.loads((out / 'SUMMARY.json').read_text())
        assert not data['source_syntax_vs_elaborated_type_automatic_matcher_implemented']
        assert data['packets'][3]['status'] == 'DIAGNOSTIC_TOTAL_LIMIT_600_SECONDS'
        assert data['packets'][4]['exit_code'] == 0
        assert len(list(out.glob('*.log'))) == 5
        assert data['controls_all_as_expected']
        assert [r['expected_failure'] for r in data['packets'][:3]] == [False, True, True]
    print('PASS: exact-one active slot and negative controls, local guard, isolated timeout cleanup, both probes and all logs; no Lean invoked')

if __name__ == '__main__':
    main()
