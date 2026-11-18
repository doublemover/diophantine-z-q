#!/usr/bin/env python3
"""Non-admitted prefix observations on one authenticated hosted zero72 timeout."""
from contextlib import chdir
import json
import os
from pathlib import Path
import tempfile
import time
import diagnose_diagonal_identity as bounded
import check_progress_experiment as experiment
import validate_progress_inventory_request as request_guard
from plan_progress_inventory import selection
from diagnose_contact_refinement import baseline_evidence, ci, digest, no_compiled, require

PACKET = 'pel-original-zero-local-length-r72'
MODULE = 'FourRootActualBranchKaehler318'
SOURCE_SHA = 'ad0e867c3f2e541b11e4d5b9ecb5f5071b36c9ab6580b5a927ca603d29ac987b'
INTAKE_SHA = '426f2513d288f4b34db744c311276810e2a70323e5ca73e52857fae94d77b7af'
APPLICATION_SHA = 'd7f178dfc8c3690b82333ef5d7930efc7657d3ea0b9ff9360d71a1c951d4dec7'
SELECTION_SHA = 'd291531b2c808956614c3b020f6289f11c693022c81957ab611672d35ca74821'
BASELINE_NAMES_SHA = 'b6c17a6c237f158a624ab27d7e963195f94f3772f289c5f1a09f0bb644efdd9c'
REQUEST_ID = 'zero72-exact-prefix-observation'
BOUNDED_SHA = 'f270b32bb08b551595e4b74cfbe3cb84ed26b3eef469894a7d4a7e5c574df7f2'
LIMITS_SHA = '1d9e0fd76754d37372f24995469592a3707fe0d3ebf5c55518752449f80a3c00'
FLAGS = ['-j1', '-M', '6144', '-Ddebug.skipKernelTC=false']
SECONDS, MAX_BYTES, MAX_PROBES = 90, 2 * 1024 * 1024, 5
LABEL = 'scratch-zero72-prefixes'
SUFFIX = 'end FourRootActualBranchKaehler318\n'
# Inclusive last original line and SHA-256 of the complete scratch input.
CUTS = {
    'imports': (5, 'd711a347e26bdf44c4bfe905b1297b1618536f0cbaecb2322f382118688e192d'),
    'three_helpers': (48, '8c94efa5212c4d6d19f0a28394776d7ae30f87e04789175dc5d7ed306df297a9'),
    'all_helpers': (71, 'd1f466e5913c79e87fba154993cc5333aa8d6b85719680028098f30ba694a687'),
    'chart_setup': (113, '6beef42e8d06ae4ed88b162c91e5f6522c3865f06bb4de89339fc1f2c825905d'),
    'source_normalized': (175, '88bdfe2ea06123e5d22877343c991728ef4de76a48c712792d718307f8a2bacb'),
    'regroup_root': (203, 'd7364ca670503926c3ad8af57855bc616b2e070897be9afe92dd0e5936ba7071'),
    'source_coordinate_original': (225, '54c43e97ac8843cad6095bd73e51f6b7811d62dc073d5a04a6269ce5160cfa57'),
}


def activated(result):
    return (result.get('packet') == PACKET and
            result.get('selection', {}).get('selection_sha256') == SELECTION_SHA)


def specimens(source):
    require(digest(source) == SOURCE_SHA, 'Full source changed')
    lines = source.splitlines(keepends=True)
    texts = {}
    for key, (count, expected) in CUTS.items():
        text = ''.join(lines[:count])
        if key != 'imports':
            text += SUFFIX
        require(digest(text) == expected, 'Frozen prefix boundary changed: ' + key)
        texts[key] = text
    return texts


def choose(rows):
    """Stop at first error; for wall limits only, compare a shorter prefix."""
    if not rows:
        return 'imports'
    last = rows[-1]
    key = last['prefix']
    if last.get('limit') == 'SCRATCH_WALL_LIMIT':
        return {'all_helpers': 'three_helpers', 'source_normalized': 'chart_setup'}.get(key)
    if last.get('exit_code') != 0 or last.get('limit') is not None:
        return None
    return {'imports': 'all_helpers', 'all_helpers': 'source_normalized',
            'source_normalized': 'regroup_root', 'regroup_root': 'source_coordinate_original'}.get(key)


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
    require(request.get('request_id') == REQUEST_ID and request.get('schema') == 2 and
            request.get('job_minutes') == 210 and request.get('shards') == [{'packet': PACKET, 'targets': [MODULE]}],
            'Not the exclusive prefix-diagnostic marker')
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
    require(ci.sha(folder/'APPLICATION.json') == APPLICATION_SHA, 'Application changed')
    data = json.loads((folder/'intake.json').read_text())
    chosen = selection(PACKET, INTAKE_SHA, data, [MODULE])
    require(chosen == result.get('selection') and len(chosen['selected_order']) == 45,
            'Exact 45-module dependency closure changed')
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
    require(bad['source_sha256'] == SOURCE_SHA and bad['status'] == 'timeout' and
            bad.get('exit_code') == 124 and bad.get('timed_out') is True,
            'Expected fresh production wall timeout missing')
    log = output/'logs'/(MODULE+'.log')
    require(ci.sha(log) == bad['log_sha256'] and
            log.read_bytes() == b'\nWALL_CLOCK_LIMIT_EXCEEDED\n', 'Different fresh timeout log')
    no_compiled(output/'lib', MODULE)
    audit = result['audit']
    require(audit.get('status') == 'audit_pass' and audit.get('exit_code') == 0 and
            audit.get('modules') == passed and audit.get('declarations') == 665,
            'Own successful-subset audit missing')
    audit_log = output/'logs/ExperimentAudit.log'
    require(ci.sha(audit_log) == audit['log_sha256'] and
            'EXPERIMENT_AUDIT_PASS declarations=665 modules=44' in audit_log.read_text(),
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
    require(digest('\n'.join(sorted(baseline['modules'])) + '\n') == BASELINE_NAMES_SHA,
            'Exact full packet baseline import set changed')
    for name, h in baseline['artifacts'].items():
        watched[output/name] = h
    watched[ci.ROOT/'.cache/progress-ci/receipt.json'] = baseline['receipt_sha256']
    for name in baseline['modules']:
        path = ci.PROJECT/(name+'.lean')
        watched[path] = ci.sha(path)
    # Every project import resolves to own44 or authenticated baseline, never failed draft output.
    baseline_names = set(baseline['modules'])
    for name in chosen['selected_order']:
        project_imports = {n for n in rows[name]['imports'] if '.' not in n}
        require(project_imports <= set(passed) | baseline_names, 'Unauthenticated project import')
    return specimens((folder/(MODULE+'.lean')).read_text()), watched, {
        'inventory_sha256': watched[output/'INVENTORY.json'], 'source_sha256': SOURCE_SHA,
        'selection_sha256': SELECTION_SHA, 'passed_modules': passed, 'audit_declarations': 665,
        'baseline': baseline, 'source_commit': request['source_commit'],
        'execution_commit': request['execution_commit'], 'run_id': os.environ['GITHUB_RUN_ID']}


def run(folder, output, env, result, deadline):
    if not activated(result) or os.environ.get('GITHUB_ACTIONS') != 'true' or not os.environ.get('RUNNER_TEMP'):
        return
    # Cheap opt-in: no scratch directory or log is made for an ordinary inventory.
    # The marker and its tree/parent are validated independently before any probe.
    marker = ci.ROOT/request_guard.MARKER
    if json.loads(marker.read_text()).get('request_id') != REQUEST_ID:
        return
    logs = output/'logs'/LABEL
    if logs.exists():
        return
    rows = []
    base = {'scope': 'NON_ADMITTED_EXACT_PREFIX_DIAGNOSTIC', 'packet': PACKET, 'module': MODULE,
            'production_source_changed': False, 'production_limits_changed': False,
            'writes_olean': False, 'proof_acceptance': False, 'packet_acceptance': False}
    try:
        texts, watched, evidence = validate(folder, output, result, deadline)
        with chdir(ci.PROJECT):
            exact_env, version = ci.environment(ci.PROJECT, output/'lib')
        require(exact_env.get('LEAN_PATH') == env.get('LEAN_PATH') and version == result['toolchain'],
                'Compiler environment changed')
        logs.mkdir()
        (logs/'PRE-PROBE-INVENTORY.json').write_bytes((output/'INVENTORY.json').read_bytes())
        started = time.monotonic()
        for _ in range(MAX_PROBES):
            key = choose(rows)
            if key is None:
                break
            require(key not in {r['prefix'] for r in rows}, 'Repeated probe')
            if time.time() + SECONDS + 60 >= deadline or time.monotonic() - started >= MAX_PROBES * (SECONDS + 10):
                break
            with tempfile.TemporaryDirectory(prefix='zero72-prefix-', dir=os.environ['RUNNER_TEMP']) as tmp:
                root = Path(tmp)
                path = root/(MODULE+'.lean')
                text = texts[key]
                path.write_text(text)
                log = logs/(key+'.log')
                no_compiled(root)
                row = bounded.bounded_memory(path, root, exact_env, log)
                no_compiled(root)
                no_compiled(output/'lib', MODULE)
                require(ci.sha(path) == CUTS[key][1], 'Scratch input changed')
                rows.append(dict(row, prefix=key, input_sha256=CUTS[key][1],
                                 through_original_line=CUTS[key][0], log_sha256=ci.sha(log)))
        require(all(p.is_file() and ci.sha(p) == h for p,h in watched.items()),
                'Production evidence/source/cache/artifact changed')
        ci.write_json(logs/'DIAGNOSTIC.json', dict(base, status='RECORDED' if rows else 'NO_PROBE_WINDOW',
            probe_executed=bool(rows), evidence=evidence, results=rows, strict_flags=FLAGS,
            seconds_per_probe=SECONDS, bytes_per_probe=MAX_BYTES, max_probes=MAX_PROBES,
            interpretation='Each scratch input is an exact source prefix, closed only with the original namespace end when needed. Exit, time and memory describe that cumulative prefix in its own process. A cutoff does not identify a unique cause or prove the full source.'))
    except Exception as exc:
        logs.mkdir(exist_ok=True)
        ci.write_json(logs/'DIAGNOSTIC.json', dict(base, status='SKIPPED_OR_INVALID',
            probe_executed=any(logs.glob('*.log')), reason=type(exc).__name__+': '+str(exc)))
