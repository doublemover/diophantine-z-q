#!/usr/bin/env python3
"""Hosted-only, NON-ADMITTED isolation of one exact Picard helper.

One statement-only scratch probe intentionally contains sorry. It is never an
accepted proof or imported artifact. Production source/options and normal packet
checks are unchanged. The shared bounded runner does not request an olean.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import tempfile
import diagnose_diagonal_identity as runner

ci = runner.ci
PACKET = 'contact-relative-site-descent-r83'
MODULE = 'ActualAffineEffectiveComparison318'
DEPENDENCY = 'ActualCanonicalOverlap318'
SOURCE_SHA = 'bea62a36a5337a16bb74294ced9cb67dfbfb9173eb7089b9d5aeda2a8aa921f6'
INTAKE_SHA = '1d3e917431346532c24ca2f9472adb5940bc63ed5cd67f90f4b1ba08213d56d2'
APPLICATION_SHA = '21446d16b26ef6f07227f957a16385760a9c05f345d65cb5f0cc1597c02af3d4'
SECONDS = 90
MAX_BYTES = 2 * 1024 * 1024
FLAGS = ['-j1', '-M', '6144', '-Ddebug.skipKernelTC=false']
SCOPES = 'set_option profiler true in\nset_option profiler.threshold 1 in\n'
ANCHOR = SCOPES + '/-- Check the exact reconstructed line and its original comparison while the\n'
END = '\nend ActualAffineEffectiveComparison318\n'
REQUIRED_MARKERS = [
    'PICARD_SITE_FRONTIER_04_AFTER_original_overlap_of_object_eq',
    'PICARD_SITE_PROFILER_CONTROL_BEGIN', 'PICARD_SITE_PROFILER_CONTROL_END',
    'PICARD_SITE_BODY_00_ENTER_reconstructed_actual_overlap',
    'PICARD_SITE_BODY_01_EXIT_reconstructed_actual_overlap',
]
FORBIDDEN_MARKER = 'PICARD_SITE_FRONTIER_05_AFTER_reconstructed_actual_overlap'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def segments(source):
    require(hashlib.sha256(source.encode()).hexdigest() == SOURCE_SHA, 'Frozen source changed')
    require(source.count(ANCHOR) == 1, 'Helper boundary changed')
    start = source.index(ANCHOR)
    stop = source.index('\nrun_cmd ', start)
    prefix, declaration = source[:start], source[start:stop]
    require('private lemma reconstructed_actual_overlap' in declaration, 'Wrong helper')
    require(declaration.count(' := by\n') == 1, 'Statement boundary changed')
    statement = declaration.split(' := by\n', 1)[0]
    require('sorry' not in source and 'axiom ' not in source, 'Production placeholder detected')
    return prefix, declaration, statement


def variants(source):
    prefix, declaration, statement = segments(source)
    bodies = {
        'exact_prefix_control': '',
        'exact_statement_placeholder': statement + ' := by\n  sorry\n',
        'exact_unchanged_helper': declaration,
    }
    cases = {}
    for name, body in bodies.items():
        marker = ('\nrun_cmd Lean.Elab.Command.liftIO do\n'
                  '  let out ← IO.getStderr\n'
                  '  out.putStrLn "PICARD_NONADMITTED_' + name + '_COMMAND_END"\n'
                  '  out.flush\n')
        text = prefix + body + marker + END
        expected = 1 if name == 'exact_statement_placeholder' else 0
        require(text.count('sorry') == expected and 'axiom ' not in text, 'Unexpected placeholder')
        require(FORBIDDEN_MARKER not in text, 'Later production command leaked into probe')
        cases[name] = text
    return cases


def validate(packet, output, hosted=True):
    if hosted:
        require(os.environ.get('GITHUB_ACTIONS') == 'true' and bool(os.environ.get('RUNNER_TEMP')),
                'Hosted Actions only')
    require(packet.name == PACKET, 'Unexpected packet')
    require(sha(packet/'intake.json') == INTAKE_SHA, 'Frozen intake changed')
    require(sha(packet/'APPLICATION.json') == APPLICATION_SHA, 'Frozen application changed')
    intake = json.loads((packet/'intake.json').read_text())
    for name, item in intake['files'].items():
        require(sha(packet/name) == item['sha256'], 'Source binding changed: ' + name)
    result_path = output/'RESULT.json'
    require(result_path.is_file(), 'Mandatory full packet result is missing')
    result = json.loads(result_path.read_text())
    require(result.get('packet') == PACKET and result.get('packet_sha256') == INTAKE_SHA,
            'Wrong full packet result')
    rows = result.get('commands', [])
    index = intake['order'].index(MODULE)
    require([r.get('module') for r in rows] == intake['order'][:index+1],
            'Ordinary check did not reach exactly the observed frontier')
    require(all(r.get('exit_code') == 0 for r in rows[:-1]) and rows[-1].get('exit_code') == 124,
            'Ordinary frontier outcomes changed; reassess instead of probing')
    log_path = output/'logs'/(MODULE+'.log')
    require(log_path.is_file(), 'Mandatory production log is missing')
    log = log_path.read_text()
    require(all(x in log for x in REQUIRED_MARKERS) and FORBIDDEN_MARKER not in log,
            'Observed marker boundary changed')
    positions = [log.index(x) for x in REQUIRED_MARKERS]
    require(positions == sorted(positions), 'Observed marker order changed')
    timing = re.search(r'PICARD_SITE_PROFILER_CONTROL took [0-9.eE+-]+(?:ms|s)', log)
    require(timing is not None and positions[1] < timing.start() < positions[2],
            'Native profiler positive control missing')
    require('WALL_CLOCK_LIMIT_EXCEEDED' in log, 'Production wall-limit marker missing')
    require((output/'lib'/(DEPENDENCY+'.olean')).is_file(), 'Normally compiled dependency missing')
    require(not any((output/'lib'/(MODULE+s)).exists() for s in ci.SUFFIXES),
            'Failed target produced an importable artifact; reassess')
    require(runner.original.SECONDS == SECONDS and runner.original.MAX_BYTES == MAX_BYTES,
            'Diagnostic runner caps changed')
    require(ci.FLAGS == FLAGS, 'Strict compiler flags changed')
    return variants((packet/(MODULE+'.lean')).read_text()), sha(result_path), sha(log_path)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('packet', choices=[PACKET])
    args = parser.parse_args()
    packet = ci.ROOT/'quartics/quartic-318-326/proof/experiments'/args.packet
    output = ci.ROOT/'build/progress-experiments'/args.packet
    cases, result_sha, log_sha = validate(packet, output)
    env, version = ci.environment(ci.PROJECT, output/'lib')
    logs = output/'scratch-picard-reconstructed-overlap'
    logs.mkdir(exist_ok=False)
    rows = []
    with tempfile.TemporaryDirectory(prefix='picard-nonadmitted-', dir=os.environ['RUNNER_TEMP']) as directory:
        root = Path(directory)
        for name, text in cases.items():
            source = root/(name+'.lean')
            source.write_text(text)
            (logs/(name+'.lean.txt')).write_text(text)
            row = runner.bounded_memory(source, root, env, logs/(name+'.log'))
            require(not any(p.is_file() and any(p.name.endswith(s) for s in ci.SUFFIXES)
                            for p in root.rglob('*')), 'Unexpected compiled scratch artifact')
            row.update(source_sha256=hashlib.sha256(text.encode()).hexdigest(),
                       contains_sorry=(name == 'exact_statement_placeholder'),
                       admitted=False, proof_acceptance=False)
            rows.append(row)
            print(json.dumps(row), flush=True)
    prefix, declaration, statement = segments((packet/(MODULE+'.lean')).read_text())
    ci.write_json(logs/'DIAGNOSTIC.json', {
        'scope': 'NON_ADMITTED_PICARD_HELPER_ISOLATION_ONLY',
        'packet': PACKET, 'packet_intake_sha256': INTAKE_SHA,
        'packet_application_sha256': APPLICATION_SHA,
        'full_result_sha256': result_sha, 'production_log_sha256': log_sha,
        'original_source_sha256': SOURCE_SHA,
        'prefix_sha256': hashlib.sha256(prefix.encode()).hexdigest(),
        'helper_declaration_sha256': hashlib.sha256(declaration.encode()).hexdigest(),
        'helper_statement_sha256': hashlib.sha256(statement.encode()).hexdigest(),
        'toolchain': version, 'seconds_per_probe': SECONDS, 'bytes_per_probe': MAX_BYTES,
        'variants': rows, 'full_packet_accepted': False,
        'baseline_or_experiment_accepted': False, 'writes_olean': False,
        'production_source_changed': False, 'production_limits_changed': False,
        'interpretation': 'Only completed independent process outcomes compare prefix, statement-placeholder and unchanged helper. A placeholder exit0 is not proof; missing rows/markers cannot uniquely identify kernel, finalization or asynchronous work.',
    })


if __name__ == '__main__':
    main()
