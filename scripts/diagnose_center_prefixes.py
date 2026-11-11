#!/usr/bin/env python3
"""Hosted-only exact-prefix center diagnostics; never an accepted proof artifact."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import diagnose_diagonal_identity as runner
ci = runner.ci
PACKET = 'height-normalized-valuative-center-r45'
SOURCE = 'IntegralOverlapRootGenerators318'
DEPENDENCY = 'ThreeRootScaledGenerators318'
SOURCE_SHA = 'e072051ee9043eab846dcaaf262396b70ff60b171ee3a67e4bb859804affdd00'
INTAKE_SHA = '2dc399ec3f8aaae3d4cf2c56a7d9eddcfe57e1454692ab615f4866fbbb24e062'
APPLICATION_SHA = '4e7790f9bf6911a034766b8388bd70823e1fe2fb71fb63eba524c8fbde412b3f'
SECONDS = 90  # Existing bounded diagnostic runner cap, below standard module cap180.

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(condition, message):
    if not condition:
        raise ValueError(message)

def variants(source):
    require(hashlib.sha256(source.encode()).hexdigest() == SOURCE_SHA, 'Frozen source changed')
    end = '\nend IntegralOverlapRootGenerators318\n'
    cuts = {
        'imports_only': (source.index('public section\n'), ''),
        'abstract_helpers': (source.index('\nvariable (R : Type*)'), end),
        'concrete_generators': (source.index('#check ("FRONTIER before finiteBaseChange_generator"'), end),
        'first_concrete_theorem': (source.index('#check ("FRONTIER before infinityBaseChange_generator"'), end),
    }
    result = {name: source[:cut] + suffix for name, (cut, suffix) in cuts.items()}
    for text in result.values():
        require('sorry' not in text and 'axiom ' not in text, 'Unexpected unproved declaration')
    return result

def validate(packet, output, hosted=True):
    if hosted:
        require(os.environ.get('GITHUB_ACTIONS') == 'true' and bool(os.environ.get('RUNNER_TEMP')), 'Hosted Actions only')
    require(sha(packet/'intake.json') == INTAKE_SHA and sha(packet/'APPLICATION.json') == APPLICATION_SHA, 'Frozen packet changed')
    intake = json.loads((packet/'intake.json').read_text())
    for name, item in intake['files'].items():
        require(sha(packet/name) == item['sha256'], 'Source binding changed: '+name)
    result_path = output/'RESULT.json'
    require(result_path.is_file(), 'Mandatory full packet result is missing')
    result = json.loads(result_path.read_text())
    require(result.get('packet') == PACKET and result.get('packet_sha256') == INTAKE_SHA, 'Wrong full packet result')
    require(any(row.get('module') == DEPENDENCY and row.get('exit_code') == 0 for row in result.get('commands', [])), 'Dependency has no successful full-check command')
    require((output/'lib'/(DEPENDENCY+'.olean')).is_file(), 'Genuinely compiled dependency is missing')
    require(runner.original.SECONDS == SECONDS, 'Diagnostic wall cap changed')
    return variants((packet/(SOURCE+'.lean')).read_text()), sha(result_path)

def main():
    p = argparse.ArgumentParser();p.add_argument('packet', choices=[PACKET]);a = p.parse_args()
    packet = ci.ROOT/'quartics/quartic-318-326/proof/experiments'/a.packet
    output = ci.ROOT/'build/progress-experiments'/a.packet
    cases, result_sha = validate(packet, output)
    env, version = ci.environment(ci.PROJECT, output/'lib')
    logs = output/'scratch-center-prefix-diagnostics';logs.mkdir(exist_ok=False)
    rows = []
    with tempfile.TemporaryDirectory(prefix='center-prefix-nonadmitted-', dir=os.environ['RUNNER_TEMP']) as directory:
        root = Path(directory)
        for name, text in cases.items():
            source = root/(name+'.lean');source.write_text(text)
            row = runner.bounded_memory(source, root, env, logs/(name+'.log'))
            row['source_sha256'] = hashlib.sha256(text.encode()).hexdigest()
            rows.append(row);print(json.dumps(row), flush=True)
    ci.write_json(logs/'DIAGNOSTIC.json', {
        'scope': 'NON_ADMITTED_EXACT_PREFIX_ONLY_NOT_FULL_CENTER_ACCEPTANCE',
        'packet': PACKET, 'packet_intake_sha256': INTAKE_SHA,
        'full_result_sha256': result_sha, 'original_source_sha256': SOURCE_SHA,
        'toolchain': version, 'seconds_per_prefix': SECONDS, 'variants': rows,
        'full_packet_accepted': False, 'baseline_or_experiment_accepted': False,
        'writes_olean': False, 'production_source_changed': False,
    })
if __name__ == '__main__':
    main()
