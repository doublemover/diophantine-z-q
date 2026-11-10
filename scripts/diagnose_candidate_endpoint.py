#!/usr/bin/env python3
"""Hosted-only no-sorry replay of the exact r27 endpoint and subsequent edge.

Separate from the original r26 scratch bisection. No olean, cache, admission,
production-source mutation, or proof-acceptance receipt is produced.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import diagnose_original_endpoint as original

ci = original.ci
PACKET = 'contact-relative-site-descent-r27'
SOURCE_SHA = '46d0c1fb3754cab21f17f2c96afa60ff422b41a7b71802f89bc16286295b072c'


def variants(source):
    assert 'private lemma associate_endpoint' in source
    start = source.index('private lemma endpoint_square')
    stop = source.index('\nrun_cmd ', start)
    # Exact endpoint declaration and all original predecessors, stopping
    # before the next edge declaration. End marker alone was not acceptance.
    prefix = source[:stop]
    prefix = prefix.replace('set_option stderrAsMessages false\n',
        'set_option stderrAsMessages false\nset_option profiler true\n'
        'set_option profiler.threshold 0\n', 1)
    assert 'sorry' not in prefix
    endpoint_only = prefix + '\nend OriginalGeometricEdge318\n'
    edge_start = source.index('lemma edge_to_module', stop)
    edge_stop = source.index('\nrun_cmd ', edge_start)
    edge = source[edge_start:edge_stop]
    # The original candidate edge proof is copied byte-for-byte. Its own
    # diagnostic budget forces a flush instead of a 180-second wall kill.
    edge_profile = (prefix + '\nset_option profiler true in\n'
        'set_option profiler.threshold 0 in\n'
        'set_option maxHeartbeats 10000 in\n' + edge +
        '\nend OriginalGeometricEdge318\n')
    return {'candidate_endpoint_only': endpoint_only,
            'candidate_edge_profile10k': edge_profile}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--packet', required=True, choices=[PACKET])
    args = parser.parse_args()
    if os.environ.get('GITHUB_ACTIONS') != 'true' or not os.environ.get('RUNNER_TEMP'):
        raise RuntimeError('This diagnostic may run only on hosted GitHub Actions')
    output = ci.ROOT/'build/progress-experiments'/args.packet
    lib = output/'lib'
    if not (lib/'AffineSectionConjugation318.olean').is_file():
        raise RuntimeError('Required normally compiled predecessor is unavailable')
    path = ci.ROOT/'quartics/quartic-318-326/proof/experiments'/args.packet/'OriginalGeometricEdge318.lean'
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SOURCE_SHA:
        raise RuntimeError('Candidate source changed from independently reviewed bytes')
    env, version = ci.environment(ci.PROJECT, lib)
    logs = output/'scratch-candidate-diagnostics'
    logs.mkdir(exist_ok=False)
    rows = []
    with tempfile.TemporaryDirectory(prefix='endpoint-candidate-nonadmitted-',
                                    dir=os.environ['RUNNER_TEMP']) as directory:
        root = Path(directory)
        for name, text in variants(raw.decode()).items():
            source = root/(name+'.lean')
            source.write_text(text)
            row = original.bounded(source, root, env, logs/(name+'.log'))
            row['source_sha256'] = hashlib.sha256(text.encode()).hexdigest()
            row['contains_sorry'] = False
            rows.append(row)
            print(json.dumps(row), flush=True)
    ci.write_json(logs/'DIAGNOSTIC.json', {'scope':'NON_ADMITTED_CANDIDATE_SCRATCH_ONLY',
        'source_sha256':SOURCE_SHA, 'toolchain':version, 'variants':rows,
        'baseline_or_experiment_accepted':False, 'writes_olean':False})


if __name__ == '__main__':
    main()
