#!/usr/bin/env python3
"""Static/mock-only fallback guard tests; every subprocess entry point blocked."""
import copy
import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import diagnose_prepared_anchor_cleanup_off as d

P = Path(os.environ.get('ANCHOR_DIAGNOSTIC_TEST_PACKET', str(d.ci.ROOT / 'quartics/quartic-318-326/proof/experiments' / d.PACKET)))
S = (P / (d.MODULE + '.lean')).read_text()

class Tests(unittest.TestCase):
    def setUp(self):
        for name in ['Popen', 'run', 'call', 'check_call', 'check_output']:
            p = patch('subprocess.' + name, side_effect=AssertionError('No subprocess allowed')); p.start(); self.addCleanup(p.stop)
        p = patch.dict(os.environ, {'GITHUB_RUN_ID': 'fixture-run', 'GITHUB_SHA': 'fixture-head'}); p.start(); self.addCleanup(p.stop)

    def prepare(self, output):
        intake = json.loads((P / 'intake.json').read_text())
        order = intake['order'][:intake['order'].index(d.MODULE) + 1]
        result = {'status': 'FAILED', 'packet': d.PACKET, 'packet_sha256': d.control.INTAKE_SHA,
                  'commands': [{'module': n, 'exit_code': 1 if n == d.MODULE else 0} for n in order]}
        (output / 'RESULT.json').write_text(json.dumps(result)); (output / 'lib').mkdir(); (output / 'logs').mkdir()
        for n in order[:-1]: (output / 'lib' / (n + '.olean')).write_text('Static mocked artifact; never used by Lean')
        (output / 'logs' / (d.MODULE + '.log')).write_text(d.control.FAILURE)
        _, evidence = d.control.validate(P, output, hosted=False)
        f = output / d.control.LABEL; f.mkdir()
        (f / (d.MODULE + '.lean.txt')).write_text(d.control.specimen(S))
        (f / (d.MODULE + '.log')).write_text(d.HEADER_OK + '\n' + d.TRACE_ERROR + '\n')
        r = {'actual_run': 'fixture-run', 'actual_head': 'fixture-head', 'status': 'RECORDED',
             'probe_executed': True, 'scope': 'NON_ADMITTED_EXACT_PREPARED_ANCHOR_SIGNATURE_CLEANUP_TRACE',
             'packet': d.PACKET, 'packet_intake_sha256': d.control.INTAKE_SHA,
             'packet_application_sha256': d.control.APPLICATION_SHA,
             'original_source_sha256': d.control.SOURCE_SHA, 'scratch_source_sha256': d.control.SCRATCH_SHA,
             'strict_flags': list(d.control.EXPECTED_FLAGS), 'seconds_per_probe': 90,
             'bytes_per_probe': 2 * 1024 * 1024, 'proof_acceptance': False, 'writes_olean': False,
             'variant': {'exit_code': 1, 'limit': None, 'admitted': False, 'proof_acceptance': False},
             'evidence': evidence}
        rp = f / 'DIAGNOSTIC.json'; rp.write_text(json.dumps(r)); return rp, r

    def test_exact_scoped_specimen(self):
        t = d.specimen(S); self.assertEqual(t.replace(d.SCOPE, '', 1), S)
        self.assertEqual(t.count('set_option cleanup.letToHave false in'), 1)
        self.assertEqual(t.count('set_option pp.all true in'), 1)
        self.assertEqual(d.control.digest(t.replace('set_option pp.all true in\n', '', 1)),
                         '4498c02be67868b7615f841c9c80b4841736938469c22aca57d96b9aa8daa16a')
        self.assertEqual(d.control.digest(t), d.SCRATCH_SHA)
        self.assertNotIn('sorry', t); self.assertNotIn('axiom ', t)
        self.assertEqual(t.count('set_option maxHeartbeats 1000000'), 1)

    def test_source_drift_rejected(self):
        with self.assertRaises(ValueError): d.specimen(S + '\n')

    def test_valid_exact_same_run_control(self):
        with tempfile.TemporaryDirectory() as t:
            o = Path(t); self.prepare(o); text, evidence, artifacts = d.validate(P, o, hosted=False)
            self.assertEqual(text, d.specimen(S)); self.assertEqual(len(evidence['successful_prefix_modules']), 117)
            self.assertEqual(len(artifacts), 3)

    def test_hosted_guard_before_writes(self):
        with tempfile.TemporaryDirectory() as t, patch.object(d.ci, 'ROOT', Path(t)), patch.dict(os.environ, {}, clear=True), patch('sys.argv', ['diagnostic', d.PACKET]):
            with self.assertRaisesRegex(ValueError, 'Hosted Actions only'): d.main()
            self.assertEqual(list(Path(t).iterdir()), [])

    def test_control_script_pin(self):
        actual = d.sha
        with patch.object(d, 'sha', lambda p: 'bad' if p == Path(d.control.__file__) else actual(p)):
            with self.assertRaisesRegex(ValueError, 'control script changed'): d.validate(P, Path('/missing'), hosted=False)

    def test_control_receipt_guards(self):
        mutations = [('actual_run', 'old-run'), ('actual_head', 'old-head'), ('status', 'SKIPPED'),
                     ('probe_executed', False), ('scope', 'other'), ('packet', 'other'),
                     ('packet_intake_sha256', 'bad'), ('packet_application_sha256', 'bad'),
                     ('original_source_sha256', 'bad'), ('scratch_source_sha256', 'bad'),
                     ('strict_flags', ['-Ddebug.skipKernelTC=true']), ('seconds_per_probe', 91),
                     ('bytes_per_probe', 4 * 1024 * 1024), ('proof_acceptance', True), ('writes_olean', True)]
        with tempfile.TemporaryDirectory() as t:
            o = Path(t); rp, r = self.prepare(o)
            for key, value in mutations:
                x = copy.deepcopy(r); x[key] = value; rp.write_text(json.dumps(x))
                with self.subTest(key=key), self.assertRaises(ValueError): d.validate(P, o, hosted=False)

    def test_missing_run_identity(self):
        with tempfile.TemporaryDirectory() as t:
            o = Path(t); self.prepare(o)
            with patch.dict(os.environ, {'GITHUB_RUN_ID': ''}), self.assertRaisesRegex(ValueError, 'run identity missing'):
                d.validate(P, o, hosted=False)

    def test_variant_success_timeout_or_admission_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            o = Path(t); rp, r = self.prepare(o)
            for key, value in [('exit_code', 0), ('limit', 'SCRATCH_WALL_LIMIT'), ('admitted', True), ('proof_acceptance', True)]:
                x = copy.deepcopy(r); x['variant'][key] = value; rp.write_text(json.dumps(x))
                with self.subTest(key=key), self.assertRaises(ValueError): d.validate(P, o, hosted=False)

    def test_same_run_evidence_required(self):
        with tempfile.TemporaryDirectory() as t:
            o = Path(t); rp, r = self.prepare(o); r['evidence']['normal_result_sha256'] = 'old'; rp.write_text(json.dumps(r))
            with self.assertRaisesRegex(ValueError, 'same normal run'): d.validate(P, o, hosted=False)

    def test_required_exact_control_artifacts(self):
        with tempfile.TemporaryDirectory() as t:
            o = Path(t); self.prepare(o); f = o / d.control.LABEL
            for suffix in ['.log', '.lean.txt']:
                p = f / (d.MODULE + suffix); text = p.read_text(); p.unlink()
                with self.assertRaisesRegex(ValueError, 'trace missing'): d.validate(P, o, hosted=False)
                p.write_text(text)
            p = f / (d.MODULE + '.lean.txt'); p.write_text(p.read_text() + '\n')
            with self.assertRaisesRegex(ValueError, 'specimen changed'): d.validate(P, o, hosted=False)

    def test_exact_cleanup_stage_required(self):
        with tempfile.TemporaryDirectory() as t:
            o = Path(t); self.prepare(o); p = o / d.control.LABEL / (d.MODULE + '.log')
            for text in [d.HEADER_OK, d.TRACE_ERROR, d.HEADER_OK + '\n' + d.TRACE_ERROR + '\n[Elab.definition.value] value', 'truncated']:
                p.write_text(text)
                with self.assertRaisesRegex(ValueError, 'cleanup-stage error absent'): d.validate(P, o, hosted=False)

    def test_failed_target_artifacts_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            o = Path(t); self.prepare(o)
            for suffix in d.control.COMPILED_SUFFIXES:
                p = o / 'lib' / (d.MODULE + suffix); p.write_text('mock forbidden target')
                with self.assertRaisesRegex(ValueError, 'Unexpected compiled'): d.validate(P, o, hosted=False)
                p.unlink()

    def test_skip_runs_no_probe(self):
        with tempfile.TemporaryDirectory() as t, patch.object(d.ci, 'ROOT', Path(t)), patch.dict(os.environ, {'GITHUB_ACTIONS': 'true', 'RUNNER_TEMP': t}), patch('sys.argv', ['diagnostic', d.PACKET]), patch.object(d.control.runner, 'bounded_memory', side_effect=AssertionError('Probe must not run')):
            d.main(); r = json.loads((Path(t) / 'build/progress-experiments' / d.PACKET / d.LABEL / 'DIAGNOSTIC.json').read_text())
            self.assertEqual(r['status'], 'SKIPPED'); self.assertFalse(r['probe_executed']); self.assertFalse(r['proof_acceptance'])

    def test_mock_zero_exit_stays_nonaccepted(self):
        with tempfile.TemporaryDirectory() as t:
            root = Path(t); packet = root / 'quartics/quartic-318-326/proof/experiments' / d.PACKET
            packet.parent.mkdir(parents=True); packet.symlink_to(P, target_is_directory=True)
            output = root / 'build/progress-experiments' / d.PACKET; output.mkdir(parents=True)
            self.prepare(output)
            def mock_runner(source, scratch, env, log):
                self.assertEqual(source.read_text(), d.specimen(S))
                log.write_text('[Elab.definition.value] mocked completed value\n')
                return {'exit_code': 0, 'limit': None, 'admitted': False, 'proof_acceptance': False}
            with patch.object(d.ci, 'ROOT', root), patch.dict(os.environ, {'GITHUB_ACTIONS': 'true', 'RUNNER_TEMP': t}), patch('sys.argv', ['diagnostic', d.PACKET]), patch.object(d.ci, 'environment', return_value=({}, 'Mocked; no Lean executed')), patch.object(d.control.runner, 'bounded_memory', side_effect=mock_runner):
                d.main()
            r = json.loads((output / d.LABEL / 'DIAGNOSTIC.json').read_text())
            self.assertEqual(r['status'], 'RECORDED'); self.assertEqual(r['variant']['exit_code'], 0)
            self.assertFalse(r['proof_acceptance']); self.assertFalse(r['writes_olean'])
            self.assertFalse(r['full_packet_accepted']); self.assertEqual(r['same_run_control_plus_differential_wall_cap_seconds'], 180)
            self.assertFalse(list((output / 'lib').glob(d.MODULE + '.*')))

    def test_changed_same_run_predecessor_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            o = Path(t); self.prepare(o)
            (o / 'lib' / (d.control.DEPENDENCY + '.olean')).write_text('Changed static mock')
            with self.assertRaisesRegex(ValueError, 'same normal run'): d.validate(P, o, hosted=False)

    def test_single_runner_no_kernel_bypass(self):
        s = Path(d.__file__).read_text()
        self.assertEqual(s.count('row = control.runner.bounded_memory('), 1)
        self.assertNotIn("'-o'", s); self.assertNotIn('skipKernelTC=true', s); self.assertNotIn('proofAsSorry', s)
        self.assertEqual(d.control.SECONDS, 90); self.assertEqual(d.control.MAX_BYTES, 2 * 1024 * 1024)
        self.assertEqual(tuple(d.control.ci.FLAGS), d.control.EXPECTED_FLAGS)

if __name__ == '__main__': unittest.main()
