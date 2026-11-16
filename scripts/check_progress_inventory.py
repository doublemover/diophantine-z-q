#!/usr/bin/env python3
"""Hosted-only dependency-ready inventory; never packet acceptance or cache promotion.

No cross-run experiment artifact reuse. A successful compile may supply only
later imports in this same isolated sweep. The recursive subset audit is separate.
"""
import argparse
from contextlib import chdir
from collections import Counter
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time
import check_progress_experiment as experiment
import check_progress_lean as ci
from plan_progress_inventory import selection

SECONDS = 180
UPLOAD_RESERVE = 60
ARTIFACT_SUFFIXES = ci.SUFFIXES


def save(path, value):
    """Atomic checkpoint: interruption cannot leave a truncated inventory JSON."""
    temp = path.with_suffix('.tmp')
    temp.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    temp.replace(path)


def compile_once(source, target, root, env, logs):
    """One strict invocation, including process-group cleanup after timeout."""
    logs.mkdir(parents=True, exist_ok=True)
    command = ['lean', *ci.FLAGS, '-R', str(root)]
    if target is not None:
        target.parent.mkdir(parents=True, exist_ok=True)
        command += ['-o', str(target)]
    command.append(str(source))
    start = time.monotonic()
    timed_out = False
    log = logs / (source.stem + '.log')
    with log.open('w') as stream:
        process = subprocess.Popen(command, cwd=ci.PROJECT, env=env,
                                   stdout=stream, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        try:
            code = process.wait(timeout=SECONDS)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            code = 124
            stream.write('\nWALL_CLOCK_LIMIT_EXCEEDED\n')
        except BaseException:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            raise
    return {'command': command, 'exit_code': code, 'timed_out': timed_out,
            'seconds': round(time.monotonic() - start, 3),
            'log_sha256': ci.sha(log)}


def inventory(folder, data, output, lib, env, result, deadline, compile_fn=compile_once,
              clock=time.time, observer=None):
    """Pure scheduling seam: tests replace compilation, never execute Lean."""
    names = set(data['order'])
    rows = result['modules']
    successful = []
    logs = output / 'logs'
    quarantine = output / 'quarantine'
    quarantine.mkdir()
    checkpoint = lambda: save(output / 'INVENTORY.json', result)
    try:
        for name in data['order']:
            row = rows[name]
            if row['status'] == 'not_selected':
                continue
            dependencies = sorted(set(row['imports']) & names)
            blockers = [d for d in dependencies if rows[d]['status'] != 'compile_pass']
            if blockers:
                causes = sorted({c for d in blockers
                                 for c in rows[d].get('root_causes', [d])})
                row.update(status='blocked_by_import', direct_blockers=blockers,
                           root_causes=causes,
                           blocker_statuses={c: rows[c]['status'] for c in causes})
                checkpoint()
                continue
            if clock() + 2 * SECONDS + UPLOAD_RESERVE > deadline:
                row.update(status='not_attempted_budget', root_causes=[name])
                checkpoint()
                continue
            # Even a stale output from a prior local invocation must not be usable.
            if any(p.exists() for p in ci.artifact_paths(lib, name).values()):
                raise ValueError('Unexpected preexisting experiment artifact: ' + name)
            work = quarantine / name
            work.mkdir()
            row.update(status='running', root_causes=[name])
            checkpoint()
            try:
                details = compile_fn(folder / (name + '.lean'), work / (name + '.olean'),
                                     folder, env, logs)
                row.update(details)
                if details['exit_code']:
                    status = ('timeout' if details.get('timed_out') else
                              'process_error' if details['exit_code'] < 0 else 'compiler_error')
                    row.update(status=status)
                else:
                    artifacts = ci.artifact_hashes(work, name)
                    # Failed or incomplete outputs are never copied into LEAN_PATH.
                    ci.copy_artifacts(work, lib, name, artifacts)
                    row.update(status='compile_pass', artifacts=artifacts, root_causes=[],
                               dependency_artifacts={d: rows[d]['artifacts'] for d in dependencies})
                    successful.append(name)
            finally:
                shutil.rmtree(work)
            checkpoint()
        result['audit'] = {'status': 'not_run_empty', 'modules': successful}
        if successful:
            if clock() + SECONDS + UPLOAD_RESERVE > deadline:
                result['audit']['status'] = 'not_attempted_budget'
            else:
                audit = output / 'ExperimentAudit.lean'
                audit.write_text(experiment.audit_text(successful))
                result['audit']['status'] = 'running'
                checkpoint()
                details = compile_fn(audit, None, output, env, logs)
                result['audit'].update(details)
                text = (logs / 'ExperimentAudit.log').read_text()
                match = re.search(r'EXPERIMENT_AUDIT_PASS declarations=(\d+) modules=(\d+)', text)
                if details['exit_code'] == 0 and match and int(match[2]) == len(successful):
                    result['audit'].update(status='audit_pass', declarations=int(match[1]))
                else:
                    result['audit']['status'] = 'timeout' if details.get('timed_out') else 'audit_failed'
        result['status'] = 'INVENTORY_RECORDED'
        if observer is not None:
            checkpoint()
            try:
                observer(folder, output, env, result, deadline)
            except Exception as error:
                # Observation never changes accounting or bypasses finally cleanup.
                print('Non-admitted inventory observation skipped: ' + str(error), flush=True)
    except BaseException as error:
        result.update(status='INVENTORY_ERROR', error=type(error).__name__ + ': ' + str(error))
        for name, row in rows.items():
            if row['status'] == 'running':
                row.update(status='interrupted', root_causes=[name])
            elif row['status'] == 'pending':
                row.update(status='not_attempted_interrupted', root_causes=[name])
        if result.get('audit', {}).get('status') == 'running':
            result['audit']['status'] = 'interrupted'
        raise
    finally:
        # No experiment binary is published or persisted for cross-run reuse in v1.
        for name in names:
            for path in ci.artifact_paths(lib, name).values():
                path.unlink(missing_ok=True)
        shutil.rmtree(quarantine, ignore_errors=True)
        result['counts'] = dict(Counter(r['status'] for r in rows.values()))
        result['dependency_ready_inventory_complete'] = not any(
            r['status'] in ('pending', 'running', 'interrupted', 'not_attempted_budget', 'not_attempted_interrupted', 'setup_error')
            for r in rows.values())
        result['selected_dependency_ready_inventory_complete'] = result['dependency_ready_inventory_complete']
        result['dependency_ready_inventory_complete'] = (result['dependency_ready_inventory_complete'] and
            all(r['status'] != 'not_selected' for r in rows.values()))
        result['all_packet_modules_compiled'] = len(successful) == len(names)
        checkpoint()


def observe_contact(folder, output, env, result, deadline):
    if (result.get('packet') != 'contact-original-positive-generators-r103' or
        result.get('selection', {}).get('selection_sha256') !=
            '79f521a554a00b0eb325202673309b68404fe1e99df13aa3c380a7a306fdab2b'):
        return
    import diagnose_contact_refinement
    diagnose_contact_refinement.run(folder, output, env, result, deadline)


def run(args, plan):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    result = {'schema': 2, 'status': 'SETUP_PENDING', 'packet': args.packet,
              'head_sha': os.environ.get('GITHUB_SHA'), 'run_id': os.environ.get('GITHUB_RUN_ID'),
              'requested_source_commit': os.environ.get('INVENTORY_SOURCE_COMMIT'),
              'requested_source_tree': os.environ.get('INVENTORY_SOURCE_TREE'),
              'request_sha256': os.environ.get('INVENTORY_REQUEST_SHA256'),
              'baseline_snapshot': plan['snapshot'], 'baseline_key': plan['base'],
              'strict_flags': ci.FLAGS, 'module_seconds': SECONDS, 'deadline_epoch': args.deadline,
              'new_source_acceptance': False, 'packet_acceptance': False,
              'experiment_artifact_reuse': False, 'modules': {}, 'audit': {'status': 'not_run'},
              'scope': 'Diagnostic dependency-ready sweep only; ordinary full packet audit remains required'}
    save(output / 'INVENTORY.json', result)
    try:
        folder, data, direct, external = experiment.packet(args.packet, plan)
        result['packet_sha256'] = ci.sha(folder / 'intake.json')
        result['order'] = data['order']
        chosen = selection(args.packet, result['packet_sha256'], data, getattr(args, 'targets', None))
        expected = getattr(args, 'selection_sha256', None)
        if expected is not None and chosen['selection_sha256'] != expected:
            raise ValueError('Selection identity differs from the exact validated plan')
        result['selection'] = chosen
        selected = set(chosen['selected_order'])
        result['modules'] = {n: {'status': 'pending' if n in selected else 'not_selected', 'source_sha256': data['files'][n+'.lean']['sha256'],
                                'imports': sorted(data['files'][n+'.lean']['imports']),
                                'occurrence': args.packet + '/' + n} for n in data['order']}
        save(output / 'INVENTORY.json', result)
        if not args.setup_ok:
            raise ValueError('Workflow dependency source/artifact setup did not succeed; no Lean invoked')
        needed = experiment.required_baseline(plan, direct)
        lib = output / 'lib'
        lib.mkdir()
        baseline = experiment.restore_baseline(args.cache.resolve(), lib, plan, needed)
        result['verified_baseline_modules'] = baseline
        # Elan selects the exact project toolchain, not a machine-wide default.
        # Keep setup-failure accounting outside any Lake invocation.
        with chdir(ci.PROJECT):
            env, version = ci.environment(ci.PROJECT, lib)
        result['toolchain'] = version
        result['checker_sha256'] = ci.sha(Path(__file__))
        result['production_checker_sha256'] = ci.sha(Path(experiment.__file__))
        # No fallback upstream compilation with the baseline runner's 3600s cap.
        # Acquisition has already run. Missing artifacts are setup failures.
        upstream = external | set(plan['upstream']) | {'Lean.Util.CollectAxioms'}
        for dep in upstream:
            if dep.split('.')[0] in {'Lean', 'Std', 'Init'}:
                continue
            if not any((Path(p) / (dep.replace('.', '/') + '.olean')).is_file()
                       for p in env['LEAN_PATH'].split(os.pathsep)):
                raise ValueError('Missing pinned upstream artifact: ' + dep)
        result['status'] = 'INVENTORY_RUNNING'
        inventory(folder, data, output, lib, env, result, args.deadline, observer=observe_contact)
    except BaseException as error:
        if result['status'] not in ('INVENTORY_ERROR', 'INVENTORY_RECORDED'):
            result.update(status='SETUP_ERROR', error=type(error).__name__ + ': ' + str(error))
            for row in result['modules'].values():
                if row['status'] != 'not_selected':
                    row['status'] = 'setup_error'
            result['dependency_ready_inventory_complete'] = False
            save(output / 'INVENTORY.json', result)
        raise
    return result


def main():
    if not __debug__:
        raise RuntimeError('Do not use Python -O')
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet', required=True)
    p.add_argument('--cache', required=True, type=Path)
    p.add_argument('--output', required=True, type=Path)
    p.add_argument('--deadline', required=True, type=int)
    p.add_argument('--targets-json', default='null')
    p.add_argument('--selection-sha256', required=True)
    p.add_argument('--window-minutes', type=int, default=24, choices=range(24, 205))
    p.add_argument('--setup-ok', choices=['true', 'false'], required=True)
    args = p.parse_args()
    args.setup_ok = args.setup_ok == 'true'
    args.targets = json.loads(args.targets_json)
    if not re.fullmatch('[0-9a-f]{64}', args.selection_sha256):
        raise ValueError('Expected full selection SHA256')
    if os.environ.get('GITHUB_ACTIONS') != 'true':
        raise RuntimeError('Compiler inventory is hosted-only; use mocked unit tests locally')
    if args.deadline > time.time() + args.window_minutes * 60:
        raise ValueError('Inventory deadline exceeds the explicit bounded inventory job window')
    ci.check_sources(ci.PROJECT)
    result = run(args, ci.derive_plan(early_depth=7))
    # A diagnostic run never declares PASS, even when every compile succeeds.
    incomplete = not result['selected_dependency_ready_inventory_complete']
    failures = any(r['status'] not in ('compile_pass', 'not_selected') for r in result['modules'].values())
    audit_failed = result['audit']['status'] != 'audit_pass'
    return 1 if incomplete or failures or audit_failed else 0


if __name__ == '__main__':
    raise SystemExit(main())
