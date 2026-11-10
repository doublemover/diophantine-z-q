#!/usr/bin/env python3
"""Hosted-only scratch bisection of the r27 edge elaboration.

Original endpoint and source bytes remain immutable. Diagnostic sorry occurs
only in RUNNER_TEMP statement-only source, never in an admitted packet.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import diagnose_candidate_endpoint as candidate
import diagnose_original_endpoint as original
ci = original.ci
PACKET = candidate.PACKET
SOURCE_SHA = candidate.SOURCE_SHA


def variants(source):
    prefix = candidate.variants(source)['candidate_endpoint_only']
    prefix = prefix.removesuffix('\nend OriginalGeometricEdge318\n')
    start = source.index('lemma edge_to_module')
    stop = source.index('\nrun_cmd ', start)
    edge = source[start:stop]
    statement, term = edge.split(' :=\n', 1)
    scopes = ('\nset_option profiler true in\nset_option profiler.threshold 0 in\n'
              'set_option diagnostics true in\nset_option maxHeartbeats 10000 in\n')
    end = '\nend OriginalGeometricEdge318\n'
    return {
        'edge_statement_only': (prefix + scopes + statement + ' := by\n  sorry\n' + end, True),
        'edge_inferred_rhs': (prefix + scopes + 'private def inferred_edge :=\n' + term + end, False),
        'edge_original_diagnostics': (prefix + scopes + edge + end, False),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--packet', required=True, choices=[PACKET])
    args = parser.parse_args()
    if os.environ.get('GITHUB_ACTIONS') != 'true' or not os.environ.get('RUNNER_TEMP'):
        raise RuntimeError('This diagnostic may run only on hosted GitHub Actions')
    output = ci.ROOT/'build/progress-experiments'/args.packet
    lib = output/'lib'
    if not (lib/'AffineSectionConjugation318.olean').is_file():
        raise RuntimeError('Normally compiled predecessor is unavailable')
    source = ci.ROOT/'quartics/quartic-318-326/proof/experiments'/args.packet/'OriginalGeometricEdge318.lean'
    raw = source.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SOURCE_SHA:
        raise RuntimeError('Candidate source changed from reviewed bytes')
    env, version = ci.environment(ci.PROJECT, lib)
    logs = output/'scratch-edge-elaboration'
    logs.mkdir(exist_ok=False)
    rows = []
    with tempfile.TemporaryDirectory(prefix='edge-elaboration-nonadmitted-',
                                    dir=os.environ['RUNNER_TEMP']) as directory:
        root = Path(directory)
        for name, (text, contains_sorry) in variants(raw.decode()).items():
            scratch = root/(name+'.lean')
            scratch.write_text(text)
            row = original.bounded(scratch, root, env, logs/(name+'.log'))
            row['source_sha256'] = hashlib.sha256(text.encode()).hexdigest()
            row['contains_sorry'] = contains_sorry
            rows.append(row)
            print(json.dumps(row), flush=True)
    ci.write_json(logs/'DIAGNOSTIC.json', {'scope':'NON_ADMITTED_EDGE_BISECTION_ONLY',
        'source_sha256': SOURCE_SHA, 'toolchain':version, 'variants':rows,
        'baseline_or_experiment_accepted':False, 'writes_olean':False})


if __name__ == '__main__':
    main()
