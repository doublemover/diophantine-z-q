#!/usr/bin/env python3
"""One hosted-only differential; exact theorem/proof, optional cleanup disabled.
Never a production repair, proof-acceptance receipt, cache input or olean producer.
"""
import argparse
import json
import os
from pathlib import Path
import tempfile
import diagnose_prepared_anchor_elaboration as control

ci = control.ci
PACKET = control.PACKET
MODULE = control.MODULE
CONTROL_SCRIPT_SHA = '0f088e409f3450949f3a08a0d9dd2e5f4a14e6bef360921ddf76ec34695ba51b'
SCOPE = 'set_option cleanup.letToHave false in\n' + control.SCOPE
SCRATCH_SHA = '4498c02be67868b7615f841c9c80b4841736938469c22aca57d96b9aa8daa16a'
LABEL = 'scratch-prepared-anchor-cleanup-off'
TRACE_ERROR = '[Meta.letToHave] 💥️ unknown free variable `_fvar.499`'
HEADER_OK = '[Elab.definition.header] ✅️ PreparedAnchorSource318.current_source_prepared_anchor'
require = control.require
sha = control.sha


def specimen(source):
    control.specimen(source)  # Frozen exact original source and trace-only specimen.
    text = source.replace(control.TARGET, SCOPE + control.TARGET, 1)
    require(text.replace(SCOPE, '', 1) == source, 'Statement or proof changed')
    require(control.digest(text) == SCRATCH_SHA, 'Frozen differential specimen changed')
    require('sorry' not in text and 'axiom ' not in text, 'Unproved declaration')
    return text


def validate(packet, output, hosted=True):
    require(sha(Path(control.__file__)) == CONTROL_SCRIPT_SHA, 'Trace-only control script changed')
    _, evidence = control.validate(packet, output, hosted)
    folder = output / control.LABEL
    rp = folder / 'DIAGNOSTIC.json'
    lp = folder / (MODULE + '.log')
    sp = folder / (MODULE + '.lean.txt')
    require(rp.is_file() and lp.is_file() and sp.is_file(), 'Fresh own cleanup trace missing')
    r = json.loads(rp.read_text())
    require(bool(os.environ.get('GITHUB_RUN_ID')) and bool(os.environ.get('GITHUB_SHA')),
            'Current hosted run identity missing')
    require(r.get('actual_run') == os.environ['GITHUB_RUN_ID'] and
            r.get('actual_head') == os.environ['GITHUB_SHA'], 'Historical or foreign cleanup trace')
    require(r.get('status') == 'RECORDED' and r.get('probe_executed') is True,
            'Cleanup trace was not executed')
    require(r.get('scope') == 'NON_ADMITTED_EXACT_PREPARED_ANCHOR_SIGNATURE_CLEANUP_TRACE' and
            r.get('packet') == PACKET and r.get('packet_intake_sha256') == control.INTAKE_SHA and
            r.get('packet_application_sha256') == control.APPLICATION_SHA,
            'Cleanup trace scope or packet changed')
    require(r.get('original_source_sha256') == control.SOURCE_SHA and
            r.get('scratch_source_sha256') == control.SCRATCH_SHA and sha(sp) == control.SCRATCH_SHA,
            'Cleanup trace specimen changed')
    require(r.get('strict_flags') == list(control.EXPECTED_FLAGS) and
            r.get('seconds_per_probe') == control.SECONDS and
            r.get('bytes_per_probe') == control.MAX_BYTES,
            'Cleanup trace strict flags or caps changed')
    require(r.get('proof_acceptance') is False and r.get('writes_olean') is False,
            'Cleanup trace is not quarantined')
    v = r.get('variant', {})
    require(v.get('exit_code') == 1 and v.get('limit') is None and
            v.get('admitted') is False and v.get('proof_acceptance') is False,
            'Cleanup trace did not have the required bounded failure')
    require(r.get('evidence') == evidence, 'Cleanup trace does not bind this same normal run')
    log = lp.read_text()
    require(HEADER_OK in log and TRACE_ERROR in log and '[Elab.definition.value]' not in log,
            'Exact pre-value cleanup-stage error absent')
    return specimen((packet / (MODULE + '.lean')).read_text()), evidence, {
        str(p.relative_to(output)): sha(p) for p in (rp, lp, sp)}


def main():
    parser = argparse.ArgumentParser(); parser.add_argument('packet', choices=[PACKET]); a = parser.parse_args()
    # This guard precedes every diagnostic write, including a SKIP receipt.
    require(os.environ.get('GITHUB_ACTIONS') == 'true' and bool(os.environ.get('RUNNER_TEMP')),
            'Hosted Actions only')
    packet = ci.ROOT / 'quartics/quartic-318-326/proof/experiments' / a.packet
    output = ci.ROOT / 'build/progress-experiments' / a.packet
    logs = output / LABEL; logs.mkdir(parents=True, exist_ok=False)
    base = {'scope': 'NON_ADMITTED_EXACT_PREPARED_ANCHOR_CLEANUP_OFF_DIFFERENTIAL',
            'packet': PACKET, 'actual_head': os.environ.get('GITHUB_SHA'),
            'actual_run': os.environ.get('GITHUB_RUN_ID'),
            'packet_intake_sha256': control.INTAKE_SHA,
            'packet_application_sha256': control.APPLICATION_SHA,
            'original_source_sha256': control.SOURCE_SHA, 'scratch_source_sha256': SCRATCH_SHA,
            'production_source_changed': False, 'production_limits_changed': False,
            'full_packet_accepted': False, 'proof_acceptance': False, 'writes_olean': False,
            'optional_elaborator_cleanup_disabled_in_scratch_only': True}
    try:
        text, evidence, control_artifacts = validate(packet, output)
    except (ValueError, OSError, KeyError, json.JSONDecodeError) as exc:
        ci.write_json(logs / 'DIAGNOSTIC.json', dict(base, status='SKIPPED',
            reason=str(exc), probe_executed=False))
        print('PreparedAnchor cleanup-off differential skipped: ' + str(exc), flush=True)
        return
    env, version = ci.environment(ci.PROJECT, output / 'lib')
    (logs / (MODULE + '.lean.txt')).write_text(text)
    with tempfile.TemporaryDirectory(prefix='prepared-anchor-cleanup-off-nonadmitted-',
                                    dir=os.environ['RUNNER_TEMP']) as t:
        root = Path(t); control.no_compiled(root); control.no_compiled(output / 'lib', MODULE)
        source = root / (MODULE + '.lean'); source.write_text(text)
        row = control.runner.bounded_memory(source, root, env, logs / (MODULE + '.log'))
        control.no_compiled(root); control.no_compiled(output / 'lib', MODULE)
        require(sha(output / 'RESULT.json') == evidence['normal_result_sha256'], 'Production result changed')
        require(sha(output / 'logs' / (MODULE + '.log')) == evidence['normal_failure_log_sha256'],
                'Production log changed')
        require(sha(packet / (MODULE + '.lean')) == control.SOURCE_SHA, 'Production source changed')
        for name, expected in evidence['same_run_predecessor_artifacts'].items():
            require(sha(output / name) == expected, 'Compiled predecessor changed: ' + name)
        for name, expected in control_artifacts.items():
            require(sha(output / name) == expected, 'Trace-only control artifact changed: ' + name)
    ci.write_json(logs / 'DIAGNOSTIC.json', dict(base, status='RECORDED', probe_executed=True,
        toolchain=version, strict_flags=list(control.EXPECTED_FLAGS),
        seconds_per_probe=control.SECONDS, bytes_per_probe=control.MAX_BYTES,
        probe_wall_cap_sum_seconds=control.SECONDS,
        same_run_control_plus_differential_wall_cap_seconds=2 * control.SECONDS,
        evidence=evidence, trace_only_control_artifacts=control_artifacts, variant=row,
        interpretation='Only the optional let-to-have cleanup is disabled in a separate scratch '
        'specimen with the exact theorem statement/proof and strict kernel checking. '
        'Compare completed header/value traces, exit and later errors. Even exit zero is '
        'diagnostic only: no production repair, emitted olean, recursive audit or proof acceptance.'))

if __name__ == '__main__':
    main()
