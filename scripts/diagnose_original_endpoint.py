#!/usr/bin/env python3
"""Hosted-only, non-admitted scratch bisection of OriginalGeometricEdge.endpoint_square.

Never writes an olean, accepted source, cache or admission receipt. A successful
scratch compile containing sorry is diagnostic evidence only, never a proof.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import selectors
import subprocess
import tempfile
import time
import check_progress_lean as ci

PACKET = 'contact-relative-site-descent-r26'
SOURCE_SHA = '38cdcc5dfaac34c63773b74aaf1537f6a8e638a80942021ce954739c2769f204'
MAX_BYTES = 2 * 1024 * 1024
SECONDS = 90


def variants(source):
    anchor = 'private lemma endpoint_square'
    start = source.index(anchor)
    stop = source.index('\nrun_cmd ', start)
    declaration = source[start:stop].rstrip()
    statement, proof = declaration.split(' := by\n', 1)
    prefix = source[:start]
    scopes = ('set_option profiler true in\n'
              'set_option trace.Meta.Tactic.simp.rewrite true in\n'
              'set_option maxHeartbeats 10000 in\n')
    assert prefix.endswith(scopes), 'Unexpected production diagnostic scopes'
    prefix = prefix[:-len(scopes)]
    # Earlier declarations now have explicit profiling so capture can be tested.
    prefix = prefix.replace('set_option stderrAsMessages false\n',
        'set_option stderrAsMessages false\nset_option profiler true\n'
        'set_option profiler.threshold 0\n', 1)
    sentinel = ('\nprivate lemma scratch_profile_sentinel (n : Nat) : n = n := by rfl\n'
        'run_cmd Lean.Elab.Command.liftIO do\n'
        '  let out ← IO.getStderr\n'
        '  out.putStrLn "[SCRATCH_DIAGNOSTIC] fast profiler sentinel completed"\n'
        '  out.flush\n\n')
    prefix += sentinel
    base = 'set_option profiler true in\nset_option profiler.threshold 0 in\n'
    bodies = {
        'statement_sorry': '  sorry\n',
        'comparison_sorry': '  have observed := (sections_composition f m v hv L).symm\n  sorry\n',
        'simplify_comparison_sorry': '  have observed := (sections_composition f m v hv L).symm\n  simp only [endpoint,Iso.trans_hom,Functor.mapIso_hom,Iso.app_hom,pulled_object,Category.assoc] at observed\n  sorry\n',
        'exact_composition': '  exact (sections_composition f m v hv L).symm\n',
        'original_simpa': proof + '\n',
    }
    result = {'prefix_capture': prefix + '\nend OriginalGeometricEdge318\n'}
    for name, body in bodies.items():
        opts = base + ('set_option trace.Meta.Tactic.simp.rewrite true in\n'
            if name in {'original_simpa', 'simplify_comparison_sorry'} else '') + 'set_option maxHeartbeats 10000 in\n'
        result[name] = prefix + opts + statement + ' := by\n' + body + '\nend OriginalGeometricEdge318\n'
    return result


def bounded(source, root, env, log):
    command = ['lean', *ci.FLAGS, '-R', str(root), str(source)]
    start = time.monotonic()
    process = subprocess.Popen(command, cwd=ci.PROJECT, env=env,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    selector = selectors.DefaultSelector()
    selector.register(process.stdout, selectors.EVENT_READ)
    size = 0
    stopped = None
    with log.open('wb') as stream:
        while selector.get_map():
            if time.monotonic() - start > SECONDS:
                stopped = 'SCRATCH_WALL_LIMIT'
                process.kill()
                break
            events = selector.select(timeout=0.2)
            for key, _ in events:
                chunk = os.read(key.fileobj.fileno(), 65536)
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                remaining = MAX_BYTES - size
                stream.write(chunk[:remaining])
                size += min(len(chunk), remaining)
                if len(chunk) > remaining:
                    stopped = 'SCRATCH_LOG_LIMIT'
                    process.kill()
                    break
            if stopped:
                break
        process.wait(timeout=10)
        if stopped:
            stream.write(('\n' + stopped + '\n').encode())
    selector.close()
    process.stdout.close()
    return {'variant': source.stem, 'exit_code': process.returncode,
        'seconds': round(time.monotonic()-start, 3), 'bytes': size,
        'limit': stopped, 'admitted': False, 'proof_acceptance': False}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--packet', required=True, choices=[PACKET])
    args = parser.parse_args()
    if os.environ.get('GITHUB_ACTIONS') != 'true' or not os.environ.get('RUNNER_TEMP'):
        raise RuntimeError('This diagnostic may run only on hosted GitHub Actions')
    output = ci.ROOT / 'build/progress-experiments' / args.packet
    lib = output / 'lib'
    if not (lib/'AffineSectionConjugation318.olean').is_file():
        raise RuntimeError('Required normally compiled predecessor is unavailable')
    path = ci.ROOT/'quartics/quartic-318-326/proof/experiments'/args.packet/'OriginalGeometricEdge318.lean'
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SOURCE_SHA:
        raise RuntimeError('Diagnostic source changed from independently reviewed bytes')
    env, version = ci.environment(ci.PROJECT, lib)
    logs = output/'scratch-diagnostics'
    logs.mkdir(exist_ok=False)
    rows = []
    with tempfile.TemporaryDirectory(prefix='endpoint-nonadmitted-', dir=os.environ['RUNNER_TEMP']) as t:
        root = Path(t)
        for name, text in variants(raw.decode()).items():
            source = root/(name+'.lean')
            source.write_text(text)
            row = bounded(source, root, env, logs/(name+'.log'))
            row['source_sha256'] = hashlib.sha256(text.encode()).hexdigest()
            row['contains_sorry'] = name.endswith('_sorry')
            rows.append(row)
            print(json.dumps(row), flush=True)
    ci.write_json(logs/'DIAGNOSTIC.json', {'scope':'NON_ADMITTED_SCRATCH_ONLY',
        'source_sha256':SOURCE_SHA, 'toolchain':version, 'variants':rows,
        'baseline_or_experiment_accepted':False, 'writes_olean':False})


if __name__ == '__main__':
    main()
