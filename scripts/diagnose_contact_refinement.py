#!/usr/bin/env python3
"""One hosted, source-preserving observation before inventory artifact cleanup.

Never changes admission, packet acceptance, proof source, cache, or limits.
This hook is synchronous: existing inventory finally still removes all draft binaries.
"""
from contextlib import chdir
import hashlib
import json
import os
from pathlib import Path
import re
import tempfile
import time
import diagnose_diagonal_identity as bounded
import check_progress_experiment as experiment
import validate_progress_inventory_request as request_guard
from plan_progress_inventory import selection
ci = bounded.ci
PACKET = 'contact-original-positive-generators-r103'
MODULE = 'OriginalTensorUntwistRefinement318'
SOURCE_SHA = 'b8a94e1c84192875292db0ce087e6a7810d413013e6a1afd7ea50a7afb306949'
INTAKE_SHA = '7add5a1b5dbd547051e5d27f60bfcb338cb042bad4fc27cb6c93c5a0e73a434c'
SELECTION_SHA = '79f521a554a00b0eb325202673309b68404fe1e99df13aa3c380a7a306fdab2b'
BOUNDED_SHA = 'f270b32bb08b551595e4b74cfbe3cb84ed26b3eef469894a7d4a7e5c574df7f2'
LIMITS_SHA = '1d9e0fd76754d37372f24995469592a3707fe0d3ebf5c55518752449f80a3c00'
FLAGS = ['-j1', '-M', '6144', '-Ddebug.skipKernelTC=false']
SECONDS = 90
MAX_BYTES = 2 * 1024 * 1024
LABEL = 'scratch-contact-refinement'
OPTIONS = ('set_option stderrAsMessages false\nset_option diagnostics true\n'
           'set_option profiler true\nset_option profiler.threshold 10\n')
SUFFIXES = (*ci.SUFFIXES, '.ilean')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def activated(result):
    return (result.get('packet') == PACKET and
            result.get('selection', {}).get('selection_sha256') == SELECTION_SHA)


def specimen(source):
    require(digest(source) == SOURCE_SHA, 'Frozen production source changed')
    anchor = 'public section\n'
    require(source.count(anchor) == 1 and source.count('set_option maxHeartbeats 650000') == 1,
            'Frozen source boundaries or heartbeat changed')
    text = source.replace(anchor, anchor + OPTIONS, 1)
    require(text.replace(OPTIONS, '', 1) == source, 'Observation changed proof source')
    return text


def no_compiled(path, module='*'):
    require(not [str(p) for suffix in SUFFIXES for p in path.rglob(module + suffix)],
            'Unexpected diagnostic/failed-module compiled artifact')


def baseline_evidence(output, result, plan):
    require(result.get('baseline_snapshot') == plan['snapshot'] and
            result.get('baseline_key') == plan['base'], 'Baseline plan identity changed')
    receipt_path = ci.ROOT / '.cache/progress-ci/receipt.json'
    receipt = json.loads(receipt_path.read_text())
    identity = {'schema': ci.SCHEMA, 'status': 'PASS', 'base': plan['base'],
                'snapshot': plan['snapshot'], 'scope': 'Complete source coverage and recursive axiom audit'}
    require(all(receipt.get(k) == v for k, v in identity.items()), 'Full audited baseline identity changed')
    require(re.fullmatch('[0-9a-f]{64}', receipt.get('audit_result_sha256', '')) is not None,
            'Baseline audit binding unavailable')
    recorded = result.get('verified_baseline_modules', {})
    require(bool(recorded) and set(recorded) <= set(plan['module_order']), 'Baseline module set invalid')
    built = {}
    artifacts = {}
    for name in plan['module_order']:
        if name not in recorded:
            continue
        entry = receipt.get('modules', {}).get(name)
        require(entry == recorded[name], 'Copied baseline receipt entry differs: ' + name)
        require(ci.reusable(entry, name, plan, ci.ROOT / '.cache/progress-ci/lib', built),
                'Stale/corrupt baseline artifact: ' + name)
        require(ci.artifact_hashes(output / 'lib', name) == entry['files'],
                'Copied same-run baseline bytes differ: ' + name)
        built[name] = entry
        artifacts.update({'lib/' + name.replace('.', '/') + s: h for s, h in entry['files'].items()})
    return {'receipt_sha256': ci.sha(receipt_path), 'audit_result_sha256': receipt['audit_result_sha256'],
            'scope': 'AUTHENTICATED_REUSED_BASELINE_NOT_FRESH_COMPILATION',
            'modules': list(built), 'artifacts': artifacts}


def validate(folder, output, result, deadline):
    require(os.environ.get('GITHUB_ACTIONS') == 'true' and bool(os.environ.get('RUNNER_TEMP')),
            'Hosted Actions only')
    require(activated(result) and folder.name == PACKET, 'Wrong packet or selection')
    require(ci.FLAGS == FLAGS and bounded.original.SECONDS == SECONDS and
            bounded.original.MAX_BYTES == MAX_BYTES, 'Strict flags or scratch caps changed')
    require(ci.sha(Path(bounded.__file__)) == BOUNDED_SHA and
            ci.sha(Path(bounded.original.__file__)) == LIMITS_SHA, 'Bounded runner changed')
    require(time.time() + SECONDS + 60 < deadline, 'Insufficient original inventory window')
    event = json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_text())
    request = request_guard.validate(ci.ROOT, event, os.environ)
    require(result.get('head_sha') == request['execution_commit'] == os.environ['GITHUB_SHA'] and
            str(result.get('run_id')) == os.environ['GITHUB_RUN_ID'], 'Not own fresh run')
    require(result.get('requested_source_commit') == request['source_commit'] and
            result.get('requested_source_tree') == request['source_tree'] and
            result.get('request_sha256') == request['marker_sha256'], 'Source/marker binding changed')
    require(result.get('strict_flags') == FLAGS and result.get('module_seconds') == 180 and
            result.get('experiment_artifact_reuse') is False and
            result.get('packet_acceptance') is False and result.get('new_source_acceptance') is False,
            'Inventory acceptance/strict policy differs')
    require(result.get('checker_sha256') == ci.sha(Path(__file__).with_name('check_progress_inventory.py')) and
            result.get('production_checker_sha256') == ci.sha(Path(experiment.__file__)),
            'Own checker identity changed')
    require(result.get('status') == 'INVENTORY_RECORDED', 'Inventory did not finish')
    require(ci.sha(folder/'intake.json') == INTAKE_SHA == result.get('packet_sha256'), 'Intake changed')
    data = json.loads((folder/'intake.json').read_text())
    chosen = selection(PACKET, INTAKE_SHA, data, [MODULE])
    require(chosen == result.get('selection') and len(chosen['selected_order']) == 44,
            'Exact 44-module dependency closure changed')
    require(result.get('order') == data['order'] and set(result['modules']) == set(data['order']),
            'Inventory source coverage changed')
    watched = {output/'INVENTORY.json': ci.sha(output/'INVENTORY.json'),
               folder/'intake.json': INTAKE_SHA, folder/'APPLICATION.json': ci.sha(folder/'APPLICATION.json')}
    require(json.loads((output/'INVENTORY.json').read_text()) == result, 'In-memory/checkpoint mismatch')
    rows = result['modules']
    passed = [n for n in chosen['selected_order'] if n != MODULE]
    for name in data['order']:
        path = folder/(name+'.lean')
        require(ci.sha(path) == rows[name]['source_sha256'] == data['files'][name+'.lean']['sha256'],
                'Production source identity changed: ' + name)
        require(rows[name]['imports'] == sorted(data['files'][name+'.lean']['imports']),
                'Import metadata changed: ' + name)
        watched[path] = ci.sha(path)
        if name not in chosen['selected_order']:
            require(rows[name]['status'] == 'not_selected', 'Unexpected selected module')
    bad = rows[MODULE]
    require(bad['source_sha256'] == SOURCE_SHA and bad['status'] == 'compiler_error' and
            bad.get('exit_code') == 1 and bad.get('timed_out') is False,
            'Expected fresh deterministic compiler error missing')
    log = output/'logs'/(MODULE+'.log')
    require(ci.sha(log) == bad['log_sha256'] and
            '(deterministic) timeout at `whnf`, maximum number of heartbeats (650000)' in log.read_text(),
            'Exact fresh whnf heartbeat error missing')
    no_compiled(output/'lib', MODULE)
    audit = result['audit']
    require(audit.get('status') == 'audit_pass' and audit.get('exit_code') == 0 and
            audit.get('modules') == passed and audit.get('declarations') == 573,
            'Own successful-subset audit missing')
    audit_log = output/'logs/ExperimentAudit.log'
    require(ci.sha(audit_log) == audit['log_sha256'] and
            'EXPERIMENT_AUDIT_PASS declarations=573 modules=43' in audit_log.read_text(),
            'Own audit log binding missing')
    watched[audit_log] = ci.sha(audit_log)
    watched[output/'ExperimentAudit.lean'] = ci.sha(output/'ExperimentAudit.lean')
    require((output/'ExperimentAudit.lean').read_text() == experiment.audit_text(passed),
            'Audit source differs from exact successful subset')
    for name in chosen['selected_order']:
        row = rows[name]
        log = output/'logs'/(name+'.log')
        require(ci.sha(log) == row['log_sha256'], 'Own log changed: ' + name)
        watched[log] = ci.sha(log)
        if name == MODULE:
            continue
        require(row['status'] == 'compile_pass' and row.get('exit_code') == 0 and
                row.get('timed_out') is False, 'Own dependency compile failed: ' + name)
        require(ci.artifact_hashes(output/'lib', name) == row['artifacts'], 'Own artifact changed: ' + name)
        deps = sorted(set(row['imports']) & set(data['order']))
        require(row.get('dependency_artifacts') == {n: rows[n]['artifacts'] for n in deps},
                'Own transitive artifact binding changed: ' + name)
        for suffix, h in row['artifacts'].items():
            watched[output/'lib'/(name+suffix)] = h
    plan = ci.derive_plan(early_depth=7)
    baseline = baseline_evidence(output, result, plan)
    for name, h in baseline['artifacts'].items():
        watched[output/name] = h
    watched[ci.ROOT/'.cache/progress-ci/receipt.json'] = baseline['receipt_sha256']
    for name in baseline['modules']:
        path = ci.PROJECT/(name+'.lean')
        watched[path] = ci.sha(path)
    # Every project import resolves to own43 or authenticated baseline, never failed draft output.
    baseline_names = set(baseline['modules'])
    for name in chosen['selected_order']:
        project_imports = {n for n in rows[name]['imports'] if '.' not in n}
        require(project_imports <= set(passed) | baseline_names, 'Unauthenticated project import')
    return specimen((folder/(MODULE+'.lean')).read_text()), watched, {
        'inventory_sha256': watched[output/'INVENTORY.json'], 'source_sha256': SOURCE_SHA,
        'selection_sha256': SELECTION_SHA, 'passed_modules': passed, 'audit_declarations': 573,
        'baseline': baseline, 'source_commit': request['source_commit'],
        'execution_commit': request['execution_commit'], 'run_id': os.environ['GITHUB_RUN_ID']}


def run(folder, output, env, result, deadline):
    """Fail closed and non-admitting; never let diagnostic failure bypass outer cleanup."""
    if not activated(result):
        return
    # Host guard precedes even a skip receipt or temporary directory.
    if os.environ.get('GITHUB_ACTIONS') != 'true' or not os.environ.get('RUNNER_TEMP'):
        return
    logs = output/LABEL
    if logs.exists():
        return
    base = {'scope': 'NON_ADMITTED_UNCHANGED_CONTACT_REFINEMENT_OBSERVATION',
            'packet': PACKET, 'module': MODULE, 'production_source_changed': False,
            'production_limits_changed': False, 'writes_olean': False,
            'proof_acceptance': False, 'packet_acceptance': False}
    try:
        text, watched, evidence = validate(folder, output, result, deadline)
        # Validate compiler/pins/search path again; no inherited unchecked project library.
        with chdir(ci.PROJECT):
            exact_env, version = ci.environment(ci.PROJECT, output/'lib')
        require(exact_env.get('LEAN_PATH') == env.get('LEAN_PATH') and version == result['toolchain'],
                'Compiler environment changed')
        logs.mkdir()
        # Preserve the pre-cleanup checkpoint; outer finally legitimately adds final accounting.
        (logs/'PRE-PROBE-INVENTORY.json').write_bytes((output/'INVENTORY.json').read_bytes())
        with tempfile.TemporaryDirectory(prefix='contact-refinement-observation-', dir=os.environ['RUNNER_TEMP']) as tmp:
            root = Path(tmp)
            path = root/(MODULE+'.lean')
            path.write_text(text)
            (logs/'observational_source.lean.txt').write_text(text)
            no_compiled(root)
            row = bounded.bounded_memory(path, root, exact_env, logs/'observational_source.log')
            no_compiled(root)
            no_compiled(output/'lib', MODULE)
            require(all(p.is_file() and ci.sha(p) == h for p, h in watched.items()),
                    'Source/result/cache/artifact changed during observation')
        ci.write_json(logs/'DIAGNOSTIC.json', dict(base, status='RECORDED', probe_executed=True,
            scratch_sha256=digest(text), strict_flags=FLAGS, seconds_per_probe=SECONDS,
            bytes_per_probe=MAX_BYTES, evidence=evidence, result=row,
            interpretation='One observational replay only. Profiles/diagnostics do not prove a cause; full exit and output are required. No result is admitted and inventory acceptance is unchanged. Outer inventory cleanup removes all draft artifacts even if this diagnostic fails.'))
    except Exception as exc:
        logs.mkdir(exist_ok=True)
        ci.write_json(logs/'DIAGNOSTIC.json', dict(base, status='SKIPPED_OR_INVALID',
            probe_executed=(logs/'observational_source.log').exists(), reason=type(exc).__name__+': '+str(exc)))
