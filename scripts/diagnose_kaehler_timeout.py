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
PACKET = 'pel-original-cotangent-hzero-forty-r69'
MODULE = 'FourRootActualBranchKaehler318'
DEPENDENCIES = {'FourRootActualBranchLocalization318','ActualEtaleFrameNormalization318','SquareCoordinateDifferential318','ActualRootPivotCoordinates318'}
BASELINE_SOURCES = {'SquareCoordinateDifferential318': 'dc7711a87960735b1682f8ccfa9275be60b5bce135ab5386b36d12f06a2e908b'}
SOURCE_SHA = '26e84b6a6e5f1d14263d71673cdfbbc520964630179cf9732fb2616b471d0b32'
SCRATCH_SHAS = {'imports_only':'f1897fcc4789b38cf94da1e8ce4cbf9876709002c2d54252ba63ae7f6f4dbb59','command_trace':'c8d21c9ffa5b1a823e088243a59c9fa296627b272e329136ffe7a9cefb8d46c2'}
INTAKE_SHA = '6e0afdf648f8afae6195ad8ac836ac706f8e804a3bdf2572ce15f292d435f442'
APPLICATION_SHA = 'bb069d50852d17b665734340b9ded0e32d373aadef7685c13e854998ee8b8128'
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

OLD_FINAL_TACTICS = '  rw [regroup_root,AlgHom.commutes,\n    IsScalarTower.algebraMap_apply (BranchBase b i) (OpenBase b i)\n      (OpenBase b i⊗[BranchBase b i]RegroupedOrder b i),AlgEquiv.commutes]\n  rfl\n'
SUBSTEP_FINAL_TACTICS = '  run_tac do\n    let emit : String → Lean.Elab.Tactic.TacticM Unit := fun label => do\n      let out ← IO.getStderr\n      out.putStrLn ("KAEHLER_SUBSTEP_" ++ label)\n      out.flush\n    emit "BEFORE_FINAL_RW"\n    Lean.Elab.Tactic.evalTactic (← `(tactic| rw [regroup_root,AlgHom.commutes,\n      IsScalarTower.algebraMap_apply (BranchBase b i) (OpenBase b i)\n        (OpenBase b i⊗[BranchBase b i]RegroupedOrder b i),AlgEquiv.commutes]))\n    emit "AFTER_FINAL_RW"\n    emit "BEFORE_FINAL_RFL"\n    Lean.Elab.Tactic.evalTactic (← `(tactic| rfl))\n    emit "AFTER_FINAL_RFL"\n'
SUBSTEP_SCOPE = 'set_option trace.Elab.definition.header true in\nset_option trace.Elab.definition.value true in\n'

def substep_specimen(text):
    """Trace the exact final two tactics, without changing their quotations.

    Markers execute inside one run_tac so the final post-rfl marker can be
    emitted even after rfl closes the last goal. No result is admitted.
    """
    target = 'lemma source_coordinate_original:'
    require(text.count(target) == 1, 'Target declaration boundary changed')
    start = text.index(target)
    end = text.index('\nrun_cmd ', start)
    declaration = text[start:end]
    before = OLD_FINAL_TACTICS
    require(declaration.count(before.rstrip('\n')) == 1, 'Final tactic sequence changed')
    after = declaration.replace(before.rstrip('\n'), SUBSTEP_FINAL_TACTICS.rstrip('\n'), 1)
    return text[:start] + SUBSTEP_SCOPE + after + text[end:]

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
    text = substep_specimen(text)
    result = {'imports_only':imports+'set_option stderrAsMessages false\n'+marker('IMPORTS_ONLY_COMPLETE')+'\n','command_trace':text}
    require({k:digest(v) for k,v in result.items()} == SCRATCH_SHAS, 'Reviewed specimen changed')
    return result

def baseline_dependency_evidence(output, result, successful_prefix):
    """Read-only authentication of the one direct import from the audited baseline.

    This repeats cache provenance checks against the same job's copied library;
    it does not compile, copy, repair, or promote any artifact.
    """
    missing = DEPENDENCIES - set(successful_prefix)
    require(missing == set(BASELINE_SOURCES), 'Unexpected dependency outside successful prefix')
    plan = ci.derive_plan()
    require(result.get('baseline_snapshot') == plan['snapshot'] and
            result.get('baseline_modules') == len(plan['module_order']),
            'Own normal baseline identity changed')
    require(missing <= set(plan['module_keys']), 'Required import is not an accepted baseline module')
    source_bindings = {}
    for name, expected in BASELINE_SOURCES.items():
        source = ci.PROJECT / (name + '.lean')
        require(sha(source) == expected, 'Frozen baseline source changed: ' + name)
        source_bindings[name] = expected
    cache = ci.ROOT / '.cache/progress-ci'
    receipt_path = cache / 'receipt.json'
    receipt = json.loads(receipt_path.read_text())
    expected_receipt = {'schema': ci.SCHEMA, 'status': 'PASS', 'base': plan['base'],
        'snapshot': plan['snapshot'], 'scope': 'Complete source coverage and recursive axiom audit'}
    require(all(receipt.get(k) == v for k, v in expected_receipt.items()),
            'Audited baseline receipt identity changed')
    require(isinstance(receipt.get('audit_result_sha256'), str) and
            re.fullmatch(r'[0-9a-f]{64}', receipt['audit_result_sha256']),
            'Audited baseline result reference missing')
    needed = set()
    def visit(name):
        if name in needed:
            return
        for dependency in plan['dependencies'][name]:
            visit(dependency)
        needed.add(name)
    for name in sorted(missing):
        visit(name)
    built, artifacts = {}, {}
    for name in plan['module_order']:
        if name not in needed:
            continue
        entry = receipt.get('modules', {}).get(name)
        require(ci.reusable(entry, name, plan, cache / 'lib', built),
                'Missing, stale or corrupt audited baseline artifact: ' + name)
        require(ci.artifact_hashes(output / 'lib', name) == entry['files'],
                'Same-run copied baseline artifact differs: ' + name)
        built[name] = entry
        for suffix, value in entry['files'].items():
            artifacts['lib/' + name.replace('.', '/') + suffix] = value
    return {'scope': 'AUTHENTICATED_REUSED_BASELINE_NOT_FRESH_COMPILATION',
        'receipt_sha256': sha(receipt_path), 'audit_result_sha256': receipt['audit_result_sha256'],
        'snapshot': plan['snapshot'], 'base': plan['base'], 'source_bindings': source_bindings,
        'required_modules': [n for n in plan['module_order'] if n in needed],
        'module_keys': {n: plan['module_keys'][n] for n in plan['module_order'] if n in needed},
        'same_run_artifacts': artifacts}

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
    baseline_evidence = baseline_dependency_evidence(output, result, intake['order'][:index])
    lp = output/'logs'/(MODULE+'.log')
    require(lp.is_file() and 'WALL_CLOCK_LIMIT_EXCEEDED' in lp.read_text(), 'Exact own timeout absent')
    no_compiled(output/'lib', MODULE)
    artifacts = dict(baseline_evidence['same_run_artifacts'])
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
        'same_run_predecessor_artifacts':artifacts,
        'authenticated_reused_baseline':baseline_evidence}

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
        require(baseline_dependency_evidence(output, json.loads((output/'RESULT.json').read_text()),
                evidence['successful_prefix_modules']) == evidence['authenticated_reused_baseline'],
                'Audited baseline provenance changed during probe')
        for name, expected in evidence['same_run_predecessor_artifacts'].items():
            require(sha(output/name) == expected, 'Compiled predecessor changed: '+name)
    ci.write_json(logs/'DIAGNOSTIC.json',dict(base,status='RECORDED',probe_executed=True,
        toolchain=version,seconds_per_probe=SECONDS,probe_wall_cap_sum_seconds=2*SECONDS,
        bytes_per_probe=MAX_BYTES,strict_flags=list(EXPECTED_FLAGS),evidence=evidence,variants=rows,
        interpretation='Imports-only must complete before command tracing. Flushed final-rw/rfl markers and scoped header/value traces localize completion boundaries, not root causes. Quoted final tactics are unchanged; instrumentation itself may affect elaboration. No automatic root-cause or proof-success conclusion.'))

if __name__ == '__main__':
    main()
