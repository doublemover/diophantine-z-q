#!/usr/bin/env python3
"""Hosted-only no-sorry replay of the exact r29 named-arrow edge repair.

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
PACKET = 'contact-relative-site-descent-r29'
SOURCE_SHA = 'f1f8b9e0d7abacda01ad594d59614dc30a9a0e95210c1bfa7a3e3ec771f84e84'


def variants(source):
    endpoint = source.index('private lemma endpoint_square')
    endpoint_stop = source.index('\nrun_cmd ', endpoint)
    edge = source.index('lemma edge_to_module', endpoint_stop)
    edge_stop = source.index('\nrun_cmd ', edge)
    def close(prefix):
        prefix = prefix.replace('set_option stderrAsMessages false\n',
            'set_option stderrAsMessages false\nset_option profiler true\n'
            'set_option profiler.threshold 0\n', 1)
        assert 'sorry' not in prefix
        return prefix + '\nend OriginalGeometricEdge318\n'
    return {'named_endpoint_only': close(source[:endpoint_stop]),
            'named_through_edge': close(source[:edge_stop])}


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
    logs = output/'scratch-named-edge-diagnostics'
    logs.mkdir(exist_ok=False)
    rows = []
    with tempfile.TemporaryDirectory(prefix='named-edge-nonadmitted-',
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
    ci.write_json(logs/'DIAGNOSTIC.json', {'scope':'NON_ADMITTED_NAMED_EDGE_SCRATCH_ONLY',
        'source_sha256':SOURCE_SHA, 'toolchain':version, 'variants':rows,
        'baseline_or_experiment_accepted':False, 'writes_olean':False})


if __name__ == '__main__':
    main()
