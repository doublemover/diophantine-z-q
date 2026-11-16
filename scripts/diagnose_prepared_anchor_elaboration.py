#!/usr/bin/env python3
"""Hosted-only, one exact-source declaration-stage trace. Never a repair or acceptance."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import diagnose_diagonal_identity as runner
ci = runner.ci
PACKET = 'forward-original-weighted-weyl-r22-replay-r35'
MODULE = 'PreparedAnchorSource318'
DEPENDENCY = 'PhysicalAnchorFromHomogeneous318'
SOURCE_SHA = 'a45660c71122bdfdfd612d7436f17ff59fe3216b8f0262fa84ad4865bb5dc36e'
SCRATCH_SHA = '0bea9ef9cd747200c3e7bfb0b8f35c58ecb488c8a0bc66b1420862c4c9185a84'
INTAKE_SHA = '7b89dbce661d08a3c6b8ad70333928eec5b91d7cdbbe8e9ef56b256db9c93c90'
APPLICATION_SHA = '404de382ec3adde2ed06517463d49424203e34f6a35f5fe5a338e9dbded6860c'
RUNNER_SHA = 'f270b32bb08b551595e4b74cfbe3cb84ed26b3eef469894a7d4a7e5c574df7f2'
RUNNER_LIMITS_SHA = '1d9e0fd76754d37372f24995469592a3707fe0d3ebf5c55518752449f80a3c00'
SECONDS = 90
MAX_BYTES = 2 * 1024 * 1024
EXPECTED_FLAGS = ('-j1', '-M', '6144', '-Ddebug.skipKernelTC=false')
COMPILED_SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir')
SCOPE = ('set_option trace.Elab.definition.header true in\n'
         'set_option trace.Elab.definition.value true in\n')
TARGET = '/-- The actual fixed labels'
FAILURE = "PreparedAnchorSource318.lean:17:8: error: unknown free variable `_fvar.499`"
LABEL = 'scratch-prepared-anchor-elaboration'

def require(ok, reason):
    if not ok:
        raise ValueError(reason)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()

def no_compiled(root, module=None):
    bad = sorted(str(p.relative_to(root)) for ext in COMPILED_SUFFIXES
                 for p in root.rglob((module or '*') + ext))
    require(not bad, 'Unexpected compiled artifacts: ' + ', '.join(bad))

def specimen(source):
    require(digest(source) == SOURCE_SHA, 'Frozen target source changed')
    require(source.count(TARGET) == 1, 'Target documentation boundary changed')
    text = source.replace(TARGET, SCOPE + TARGET, 1)
    require(text.replace(SCOPE, '', 1) == source, 'Statement or proof changed')
    require(digest(text) == SCRATCH_SHA, 'Frozen scratch specimen changed')
    require('sorry' not in text and 'axiom ' not in text, 'Unproved declaration')
    return text

def validate(packet, output, hosted=True):
    if hosted:
        require(os.environ.get('GITHUB_ACTIONS') == 'true' and bool(os.environ.get('RUNNER_TEMP')),
                'Hosted Actions only')
    require(sha(Path(runner.__file__)) == RUNNER_SHA and
            sha(Path(runner.original.__file__)) == RUNNER_LIMITS_SHA, 'Bounded runner changed')
    require(tuple(ci.FLAGS) == EXPECTED_FLAGS, 'Strict compiler flags changed')
    require(runner.original.SECONDS == SECONDS and runner.original.MAX_BYTES == MAX_BYTES,
            'Existing scratch caps changed')
    require(packet.name == PACKET, 'Wrong activation packet')
    require(sha(packet/'intake.json') == INTAKE_SHA and sha(packet/'APPLICATION.json') == APPLICATION_SHA,
            'Frozen packet metadata changed')
    intake = json.loads((packet/'intake.json').read_text())
    for name, item in intake['files'].items():
        require(sha(packet/name) == item['sha256'], 'Source binding changed: ' + name)
    rp = output/'RESULT.json'
    require(rp.is_file(), 'Fresh own normal result unavailable')
    result = json.loads(rp.read_text())
    require(result.get('packet') == PACKET and result.get('packet_sha256') == INTAKE_SHA,
            'Own normal result identity changed')
    require(result.get('status') == 'FAILED', 'Own normal result is not the expected failure')
    index = intake['order'].index(MODULE)
    rows = result.get('commands', [])
    require([x.get('module') for x in rows] == intake['order'][:index+1], 'Own normal frontier changed')
    require(all(x.get('exit_code') == 0 for x in rows[:-1]) and rows[-1].get('exit_code') == 1,
            'Own normal outcomes changed')
    require(DEPENDENCY in intake['order'][:index], 'Required dependency is outside successful prefix')
    lp = output/'logs'/(MODULE+'.log')
    require(lp.is_file() and FAILURE in lp.read_text(), 'Exact own unknown-free-variable failure absent')
    no_compiled(output/'lib', MODULE)
    artifacts = {}
    for row in rows[:-1]:
        name = row['module']
        require((output/'lib'/(name+'.olean')).is_file(), 'Own normally compiled predecessor missing: '+name)
        for suffix in COMPILED_SUFFIXES:
            p = output/'lib'/(name+suffix)
            if p.is_file():
                artifacts[str(p.relative_to(output))] = sha(p)
    return specimen((packet/(MODULE+'.lean')).read_text()), {
        'normal_result_sha256':sha(rp), 'normal_failure_log_sha256':sha(lp),
        'successful_prefix_modules':[r['module'] for r in rows[:-1]],
        'same_run_predecessor_artifacts':artifacts}

def main():
    p = argparse.ArgumentParser();p.add_argument('packet', choices=[PACKET]);a = p.parse_args()
    # The hosted guard precedes all writes, even a diagnostic SKIP receipt.
    require(os.environ.get('GITHUB_ACTIONS') == 'true' and bool(os.environ.get('RUNNER_TEMP')),
            'Hosted Actions only')
    packet = ci.ROOT/'quartics/quartic-318-326/proof/experiments'/a.packet
    output = ci.ROOT/'build/progress-experiments'/a.packet
    logs = output/LABEL;logs.mkdir(parents=True, exist_ok=False)
    base = {'scope':'NON_ADMITTED_EXACT_PREPARED_ANCHOR_DECLARATION_STAGE_TRACE',
            'packet':PACKET,'packet_intake_sha256':INTAKE_SHA,'packet_application_sha256':APPLICATION_SHA,
            'original_source_sha256':SOURCE_SHA,'scratch_source_sha256':SCRATCH_SHA,
            'actual_head':os.environ.get('GITHUB_SHA'),'actual_run':os.environ.get('GITHUB_RUN_ID'),
            'production_source_changed':False,'production_limits_changed':False,
            'full_packet_accepted':False,'proof_acceptance':False,'writes_olean':False}
    try:
        text, evidence = validate(packet, output)
    except (ValueError, OSError, KeyError, json.JSONDecodeError) as exc:
        ci.write_json(logs/'DIAGNOSTIC.json', dict(base,status='SKIPPED',reason=str(exc),probe_executed=False))
        print('PreparedAnchor diagnostic skipped: '+str(exc),flush=True)
        return
    env, version = ci.environment(ci.PROJECT, output/'lib')
    (logs/(MODULE+'.lean.txt')).write_text(text)
    with tempfile.TemporaryDirectory(prefix='prepared-anchor-stage-nonadmitted-',dir=os.environ['RUNNER_TEMP']) as t:
        root=Path(t);no_compiled(root);no_compiled(output/'lib', MODULE)
        source=root/(MODULE+'.lean');source.write_text(text)
        row=runner.bounded_memory(source,root,env,logs/(MODULE+'.log'))
        no_compiled(root);no_compiled(output/'lib', MODULE)
        require(sha(output/'RESULT.json') == evidence['normal_result_sha256'], 'Production result changed')
        require(sha(output/'logs'/(MODULE+'.log')) == evidence['normal_failure_log_sha256'], 'Production log changed')
        require(sha(packet/(MODULE+'.lean')) == SOURCE_SHA, 'Production source changed')
        for name, expected in evidence['same_run_predecessor_artifacts'].items():
            require(sha(output/name) == expected, 'Compiled predecessor changed: '+name)
    ci.write_json(logs/'DIAGNOSTIC.json',dict(base,status='RECORDED',probe_executed=True,
        toolchain=version,seconds_per_probe=SECONDS,probe_wall_cap_sum_seconds=SECONDS,
        bytes_per_probe=MAX_BYTES,strict_flags=list(EXPECTED_FLAGS),evidence=evidence,variant=row,
        interpretation='Exact scoped header/value traces only. A trace entry is not completion. Missing, truncated or changed traces are inconclusive. Inspect exit, node outcomes and later errors; no automatic root-cause or proof-success conclusion.'))

if __name__ == '__main__':
    main()
