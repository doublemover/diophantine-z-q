#!/usr/bin/env python3
"""Hosted-only non-admitted exact-prefix localization, never a production repair."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import tempfile
import diagnose_diagonal_identity as runner
ci = runner.ci
PACKET = 'forward-actual-two-descent-root-divisor-orders-r15'
CONTROL_PACKET = 'forward-actual-two-descent-root-divisor-orders-r14'
MODULE = 'ScalarSmallPrimePreparation318'
DEPENDENCY = 'ScalarPackedLocalUnit318'
SOURCE_SHA = 'bf67a3951d82a74007d19237aa86334078f07aee2c6f20caafa434a6ae3d034b'
INTAKE_SHA = '9133883b2220ada796b7dbf718381173d07359b73048872bb62758ceb1f8b596'
APPLICATION_SHA = 'e6e841a067c70e947a01cea5e921129c42035f4aa0d2d02e42bfd18bf156179a'
CONTROL_SOURCE_SHA = 'f698093eaa546054c69885cbd0e4bb5bb406fdf24f29a953aeba2693f5e38428'
CONTROL_INTAKE_SHA = 'aed1df22e120eef6a2257317761ad7c19348c645ca340f8e61ff875a16ac4f54'
CONTROL_APPLICATION_SHA = '7010bb4565088ca1da63ed2fec8e37e6566515ccc6d9849d9ffe14fd9e37147a'
RUNNER_SHA = 'f270b32bb08b551595e4b74cfbe3cb84ed26b3eef469894a7d4a7e5c574df7f2'
RUNNER_LIMITS_SHA = '1d9e0fd76754d37372f24995469592a3707fe0d3ebf5c55518752449f80a3c00'
SECONDS = 90
MAX_BYTES = 2 * 1024 * 1024
EXPECTED_FLAGS = ('-j1', '-M', '6144', '-Ddebug.skipKernelTC=false')
COMPILED_SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir')
DECLARATIONS = ('integerA_shapes', 'value_scaled_unit', 'actual_multiplier_values',
                'actual_pole_thresholds', 'actual_preparation')
END = '\nend ScalarSmallPrimePreparation318\n'
PROFILE_CONTROL = '''run_cmd Lean.Elab.Command.liftIO do
  let out ← IO.getStderr
  out.putStrLn "SMALL_PRIME_PROFILER_CONTROL_BEGIN"
  out.flush
  let opts := (({} : Lean.Options).setBool `profiler true).set `profiler.threshold (0 : Nat)
  Lean.profileitIO (ε := IO.Error) "SMALL_PRIME_PROFILER_CONTROL" opts (pure ())
  out.flush
  out.putStrLn "SMALL_PRIME_PROFILER_CONTROL_END"
  out.flush
'''

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()

def no_compiled(root, module=None):
    bad = sorted(str(p.relative_to(root)) for ext in COMPILED_SUFFIXES
                 for p in root.rglob((module or '*') + ext))
    require(not bad, 'Unexpected compiled artifacts: ' + ', '.join(bad))

def marker(label):
    return ('\nrun_cmd Lean.Elab.Command.liftIO do\n  let out ← IO.getStderr\n'
            '  out.putStrLn "SMALL_PRIME_' + label + '"\n  out.flush\n')

def segments(source):
    require(digest(source) == SOURCE_SHA, 'Frozen source changed')
    require(source.endswith(END), 'Namespace end changed')
    boundaries = [source.index('/-- Exact small-prime normal forms'),
                  source.index('\nlemma value_scaled_unit') + 1,
                  source.index('\nlemma actual_multiplier_values') + 1,
                  source.index('/-- Once genuine local preparation'),
                  source.index('/-- Exact scalar preparation')]
    require(boundaries == sorted(boundaries) and len(set(boundaries)) == 5, 'Declaration order changed')
    prefix = source[:boundaries[0]]
    chunks = [source[a:b] for a, b in zip(boundaries, boundaries[1:] + [len(source)-len(END)])]
    require(prefix + ''.join(chunks) + END == source, 'Source decomposition changed')
    for name, chunk in zip(DECLARATIONS, chunks):
        require(len(re.findall(r'^(?:lemma|theorem) ', chunk, re.M)) == 1, 'Declaration span changed')
        require(re.search(r'^(?:lemma|theorem) '+name+r'\b', chunk, re.M), 'Wrong declaration')
    return prefix, chunks

def variants(source, control):
    prefix, chunks = segments(source)
    require(digest(control) == CONTROL_SOURCE_SHA, 'Historical control source changed')
    require(source == control.replace('10<inputR', '10< inputR'), 'Historical control delta changed')
    prelude = prefix + 'set_option stderrAsMessages false\n' + PROFILE_CONTROL
    cases = {}
    for count in range(6):
        text = prelude + marker('PREFIX_BEGIN_' + str(count))
        for name, chunk in zip(DECLARATIONS[:count], chunks[:count]):
            text += marker('BEFORE_' + name)
            text += 'set_option profiler true in\nset_option profiler.threshold 0 in\n' + chunk
            text += marker('AFTER_' + name)
        text += marker('PREFIX_COMMAND_END_' + str(count)) + END
        require('sorry' not in text and 'axiom ' not in text, 'Unproved declaration')
        cases['prefix_' + str(count)] = text
    # Historical r14 source is byte-exact and is compiled only into non-importable scratch.
    cases['historical_r14_exact_full_control'] = control
    return cases

def validate(packet, output, control_packet, hosted=True):
    if hosted:
        require(os.environ.get('GITHUB_ACTIONS') == 'true' and bool(os.environ.get('RUNNER_TEMP')), 'Hosted Actions only')
    require(sha(Path(runner.__file__)) == RUNNER_SHA and sha(Path(runner.original.__file__)) == RUNNER_LIMITS_SHA, 'Bounded runner implementation changed')
    require(tuple(ci.FLAGS) == EXPECTED_FLAGS, 'Strict compiler flags changed')
    require(runner.original.SECONDS == SECONDS and runner.original.MAX_BYTES == MAX_BYTES, 'Diagnostic caps changed')
    require(packet.name == PACKET and control_packet.name == CONTROL_PACKET, 'Wrong packet')
    for p, intake_sha, app_sha in [(packet, INTAKE_SHA, APPLICATION_SHA), (control_packet, CONTROL_INTAKE_SHA, CONTROL_APPLICATION_SHA)]:
        require(sha(p/'intake.json') == intake_sha and sha(p/'APPLICATION.json') == app_sha, 'Frozen packet changed')
        intake = json.loads((p/'intake.json').read_text())
        for name, item in intake['files'].items():
            require(sha(p/name) == item['sha256'], 'Source binding changed: ' + name)
    intake = json.loads((packet/'intake.json').read_text())
    rp = output/'RESULT.json'
    require(rp.is_file(), 'Mandatory own r15 result missing')
    result = json.loads(rp.read_text())
    require(result.get('packet') == PACKET and result.get('packet_sha256') == INTAKE_SHA, 'Wrong own r15 result')
    rows = result.get('commands', [])
    index = intake['order'].index(MODULE)
    require([x.get('module') for x in rows] == intake['order'][:index+1], 'Ordinary frontier changed')
    require(all(x.get('exit_code') == 0 for x in rows[:-1]) and rows[-1].get('exit_code') == 124, 'Ordinary outcomes changed')
    lp = output/'logs'/(MODULE+'.log')
    require(lp.is_file() and lp.read_text().strip() == 'WALL_CLOCK_LIMIT_EXCEEDED', 'Observed timeout log changed; reassess')
    no_compiled(output/'lib', MODULE)
    require((output/'lib'/(DEPENDENCY+'.olean')).is_file(), 'Normally compiled dependency missing')
    return variants((packet/(MODULE+'.lean')).read_text(), (control_packet/(MODULE+'.lean')).read_text()), sha(rp), sha(lp)

def main():
    p = argparse.ArgumentParser();p.add_argument('packet', choices=[PACKET]);a = p.parse_args()
    experiments = ci.ROOT/'quartics/quartic-318-326/proof/experiments'
    packet = experiments/a.packet;control = experiments/CONTROL_PACKET
    output = ci.ROOT/'build/progress-experiments'/a.packet
    cases, result_sha, log_sha = validate(packet, output, control)
    env, version = ci.environment(ci.PROJECT, output/'lib')
    logs = output/'scratch-small-prime-preparation';logs.mkdir(exist_ok=False)
    rows = []
    with tempfile.TemporaryDirectory(prefix='small-prime-nonadmitted-', dir=os.environ['RUNNER_TEMP']) as t:
        root = Path(t)
        for name, text in cases.items():
            no_compiled(root);no_compiled(output/'lib', MODULE)
            source = root/(name+'.lean');source.write_text(text)
            (logs/(name+'.lean.txt')).write_text(text)
            row = runner.bounded_memory(source, root, env, logs/(name+'.log'))
            no_compiled(root);no_compiled(output/'lib', MODULE)
            raw = (logs/(name+'.log')).read_text()
            timing = re.search(r'SMALL_PRIME_PROFILER_CONTROL took [0-9.eE+-]+(?:ms|s)', raw)
            row.update(source_sha256=digest(text), historical_source_different=(name == 'historical_r14_exact_full_control'),
                       native_profiler_control_seen=timing is not None, contains_sorry=False,
                       admitted=False, proof_acceptance=False)
            rows.append(row);print(json.dumps(row), flush=True)
        no_compiled(root);no_compiled(output/'lib', MODULE)
    prefix, chunks = segments((packet/(MODULE+'.lean')).read_text())
    ci.write_json(logs/'DIAGNOSTIC.json', {
        'scope':'NON_ADMITTED_SMALL_PRIME_EXACT_PREFIX_LOCALIZATION', 'packet':PACKET,
        'packet_intake_sha256':INTAKE_SHA,'packet_application_sha256':APPLICATION_SHA,
        'original_source_sha256':SOURCE_SHA,'historical_control_source_sha256':CONTROL_SOURCE_SHA,
        'full_result_sha256':result_sha,'production_log_sha256':log_sha,'actual_head':os.environ.get('GITHUB_SHA'),
        'exact_declaration_sha256':dict(zip(DECLARATIONS,map(digest,chunks))),
        'toolchain':version,'seconds_per_probe':SECONDS,'probe_wall_cap_sum_seconds':7*SECONDS,
        'aggregate_runtime_note':'Up to 630 seconds of probe wall caps plus setup/cleanup, separate from unchanged production180-second cap',
        'bytes_per_probe':MAX_BYTES,'strict_flags':list(EXPECTED_FLAGS),'variants':rows,
        'full_packet_accepted':False,'baseline_or_experiment_accepted':False,'writes_olean':False,
        'production_source_changed':False,'production_limits_changed':False,
        'interpretation':'Only completed independent processes compare exact cumulative prefixes. Marker emission alone cannot identify proof/kernel/finalization work. Historical r14 is source-different, never a replacement dependency or accepted proof. No scratch result is full packet/downstream acceptance.'})

if __name__ == '__main__':
    main()
