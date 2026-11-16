#!/usr/bin/env python3
"""Hosted-only, exact-source Kaehler timeout diagnostic. Never a repair or acceptance."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import re
import diagnose_diagonal_identity as runner
ci = runner.ci
PACKET = 'pel-original-cotangent-hzero-forty-r68'
MODULE = 'FourRootActualBranchKaehler318'
DEPENDENCIES = {'FourRootActualBranchLocalization318','ActualEtaleFrameNormalization318','SquareCoordinateDifferential318','ActualRootPivotCoordinates318'}
SOURCE_SHA = '26e84b6a6e5f1d14263d71673cdfbbc520964630179cf9732fb2616b471d0b32'
SCRATCH_SHAS = {'imports_only':'f1897fcc4789b38cf94da1e8ce4cbf9876709002c2d54252ba63ae7f6f4dbb59','command_trace':'324766ba3fac040b7055810250f3b2639b45786f04729f2b6c7417a41f460955'}
INTAKE_SHA = 'f17a81bd71ac81be4294e9683c91d1b7e012b723bff76afc2b55bc93cb223e9f'
APPLICATION_SHA = '3683b863c3f906b9664cca0b12aa3fbcaa85389a39666e138e7d6c2130f4296e'
RUNNER_SHA = 'f270b32bb08b551595e4b74cfbe3cb84ed26b3eef469894a7d4a7e5c574df7f2'
RUNNER_LIMITS_SHA = '1d9e0fd76754d37372f24995469592a3707fe0d3ebf5c55518752449f80a3c00'
SECONDS = 90
MAX_BYTES = 2 * 1024 * 1024
EXPECTED_FLAGS = ('-j1', '-M', '6144', '-Ddebug.skipKernelTC=false')
COMPILED_SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir')
LABEL = 'scratch-kaehler-timeout'

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

def specimens(source):
    require(digest(source) == SOURCE_SHA, 'Frozen target source changed')
    pattern = r'#eval \(do\n  let out ← IO.getStdout\n  out.putStrLn "PEL_KAEHLER_CHECKPOINT ([^"]+)"\n  out.flush : IO Unit\)'
    require(len(re.findall(pattern,source)) == 21, 'Checkpoint count changed')
    def marker(label):
        return 'run_cmd Lean.Elab.Command.liftIO do\n  let out ← IO.getStderr\n  out.putStrLn "KAEHLER_COMMAND_'+label+'"\n  out.flush'
    imports = source[:source.index('#eval')]
    text = re.sub(pattern, lambda m: marker(m[1]), source)
    text = text.replace(imports,imports+'set_option stderrAsMessages false\n',1)
    text = text.replace('public section\n','public section\nset_option profiler true\nset_option profiler.threshold 10\n',1)
    result = {'imports_only':imports+'set_option stderrAsMessages false\n'+marker('IMPORTS_ONLY_COMPLETE')+'\n','command_trace':text}
    require({k:digest(v) for k,v in result.items()} == SCRATCH_SHAS, 'Reviewed specimen changed')
    return result

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
    require(all(x.get('exit_code') == 0 for x in rows[:-1]) and rows[-1].get('exit_code') == 124,
            'Own normal outcomes changed')
    require(DEPENDENCIES <= set(intake['order'][:index]), 'Required dependency is outside successful prefix')
    lp = output/'logs'/(MODULE+'.log')
    require(lp.is_file() and 'WALL_CLOCK_LIMIT_EXCEEDED' in lp.read_text(), 'Exact own timeout absent')
    no_compiled(output/'lib', MODULE)
    artifacts = {}
    for row in rows[:-1]:
        name = row['module']
        require((output/'lib'/(name+'.olean')).is_file(), 'Own normally compiled predecessor missing: '+name)
        for suffix in COMPILED_SUFFIXES:
            p = output/'lib'/(name+suffix)
            if p.is_file():
                artifacts[str(p.relative_to(output))] = sha(p)
    return specimens((packet/(MODULE+'.lean')).read_text()), {
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
    base = {'scope':'NON_ADMITTED_KAEHLER_IMPORT_AND_COMMAND_TIMEOUT_DIAGNOSTIC',
            'packet':PACKET,'packet_intake_sha256':INTAKE_SHA,'packet_application_sha256':APPLICATION_SHA,
            'original_source_sha256':SOURCE_SHA,'scratch_source_sha256':SCRATCH_SHAS,
            'actual_head':os.environ.get('GITHUB_SHA'),'actual_run':os.environ.get('GITHUB_RUN_ID'),
            'production_source_changed':False,'production_limits_changed':False,
            'full_packet_accepted':False,'proof_acceptance':False,'writes_olean':False}
    try:
        text, evidence = validate(packet, output)
    except (ValueError, OSError, KeyError, json.JSONDecodeError) as exc:
        ci.write_json(logs/'DIAGNOSTIC.json', dict(base,status='SKIPPED',reason=str(exc),probe_executed=False))
        print('Kaehler diagnostic skipped: '+str(exc),flush=True)
        return
    env, version = ci.environment(ci.PROJECT, output/'lib')
    rows = []
    with tempfile.TemporaryDirectory(prefix='kaehler-timeout-nonadmitted-',dir=os.environ['RUNNER_TEMP']) as t:
        root=Path(t);no_compiled(root);no_compiled(output/'lib', MODULE)
        for name, specimen in text.items():
            source=root/(name+'.lean');source.write_text(specimen)
            (logs/(name+'.lean.txt')).write_text(specimen)
            row=runner.bounded_memory(source,root,env,logs/(name+'.log')); rows.append(row)
            no_compiled(root);no_compiled(output/'lib', MODULE)
            if name == 'imports_only' and (row['exit_code'] != 0 or row.get('limit') or
                'KAEHLER_COMMAND_IMPORTS_ONLY_COMPLETE' not in (logs/(name+'.log')).read_text()):
                break
        require(sha(output/'RESULT.json') == evidence['normal_result_sha256'], 'Production result changed')
        require(sha(output/'logs'/(MODULE+'.log')) == evidence['normal_failure_log_sha256'], 'Production log changed')
        require(sha(packet/(MODULE+'.lean')) == SOURCE_SHA, 'Production source changed')
        for name, expected in evidence['same_run_predecessor_artifacts'].items():
            require(sha(output/name) == expected, 'Compiled predecessor changed: '+name)
    ci.write_json(logs/'DIAGNOSTIC.json',dict(base,status='RECORDED',probe_executed=True,
        toolchain=version,seconds_per_probe=SECONDS,probe_wall_cap_sum_seconds=2*SECONDS,
        bytes_per_probe=MAX_BYTES,strict_flags=list(EXPECTED_FLAGS),evidence=evidence,variants=rows,
        interpretation='Imports-only must complete before command tracing. Last checkpoint only bounds a command interval; profiler or further evidence is needed to distinguish defeq, simp, import or evaluation cost. No automatic root-cause or proof-success conclusion.'))

if __name__ == '__main__':
    main()
