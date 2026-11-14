#!/usr/bin/env python3
"""Hosted-only, non-admitted isolation of the exact 977040de geometry frontiers.

Production modules, packets, resource limits and accepted caches are untouched.
Every probe imports only the normally compiled library and writes no olean.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import diagnose_diagonal_identity as runner

ci = runner.ci
SECONDS = 90
MAX_BYTES = 2 * 1024 * 1024
CONFIG = {
    'height-normalized-valuative-center-r64': {
        'module': 'IntegralRationalGlobalComparison318',
        'source': 'b91fb634112e38729a3339b454d5ff7dfa4477e0d84f041f50e917afbd9bedb1',
        'intake': 'dbd53af25d1d3749a043320c0649436ac5e25ddb8b7e76f164c834846e4568ae',
        'application': '9e93fd13be523d796abaf2d2fa8180aea35477042dc0d95735a0832a62169596',
        'imports': ['IntegralRationalInfinityMap318', 'IntegralRationalFiniteAtlas318',
                    'IntegralGluedModel318', 'CompletedCharacterGlobal318'],
    },
    'height-original-ks-lattice-assembly-r15': {
        'module': 'IntegralOriginalCommonRestriction318',
        'source': '872496f9df231a31c4d63d0d88c5b87676ad800790531d9980a1a6cd1e6bf699',
        'intake': '670ba8d5c5e42ad440af6621c0073fee3e6c93abc6a0f739b536a5e4b6680b04',
        'application': 'e3bbec125e26ba29accf16d5918a834cfd47d93ddebe4695f59dc6901bb0f949',
        'imports': ['LocalizedTensorRestriction318'],
    },
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def variants(packet, source):
    cfg = CONFIG[packet]
    require(hashlib.sha256(source.encode()).hexdigest() == cfg['source'], 'Frozen source changed')
    end = '\nend ' + cfg['module'] + '\n'
    opts = '\nset_option diagnostics true\nset_option profiler true\nset_option profiler.threshold 0\nset_option stderrAsMessages false\n'
    if cfg['module'] == 'IntegralRationalGlobalComparison318':
        start = source.index('/-- This equality uses all three signed infinity generators')
        stop = source.index('\ntheorem finite_square :', start)
        prefix = source[:start]
        declaration = source[start:stop]
        statement = declaration.split(' := by\n', 1)[0]
        typed = """  let f : CommRingCat.of (IntegralInfinityChart318.Order ℚ c) ⟶
      CommRingCat.of (IntegralOverlapChartMaps318.Overlap ℚ c) :=
    CommRingCat.ofHom (IntegralOverlapChartMaps318.infinityMap ℚ c).toRingHom
  let g : CommRingCat.of (InfinityOpenChart318.OpenOrder c) ⟶
      CommRingCat.of (ContactKummerOrder318.OpenOrder c) :=
    CommRingCat.ofHom (InfinityOverlapLocalization318.toOpen c)
  let eA : CommRingCat.of (IntegralInfinityChart318.Order ℚ c) ≅
      CommRingCat.of (InfinityOpenChart318.OpenOrder c) :=
    (rationalOrderEquiv c).toRingEquiv.toCommRingCatIso
  let eB : CommRingCat.of (IntegralOverlapChartMaps318.Overlap ℚ c) ≅
      CommRingCat.of (ContactKummerOrder318.OpenOrder c) :=
    (overlapEquiv c).toRingEquiv.toCommRingCatIso
"""
        square = """  have square : f ≫ eB.hom = eA.hom ≫ g := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change overlapEquiv c (IntegralOverlapChartMaps318.infinityMap ℚ c a) =
      InfinityOverlapLocalization318.toOpen c (rationalOrderEquiv c a)
    exact IntegralRationalInfinityMap318.infinity_restriction c a
"""
        helper = """  have h := spec_inverse_square
    (A := CommRingCat.of (IntegralInfinityChart318.Order ℚ c))
    (B := CommRingCat.of (IntegralOverlapChartMaps318.Overlap ℚ c))
    (C := CommRingCat.of (InfinityOpenChart318.OpenOrder c))
    (D := CommRingCat.of (ContactKummerOrder318.OpenOrder c)) f g eA eB square
"""
        wrappers = """  simpa only [overlapIso, intoInfinity, ContactOverlapMaps318.infinityInclusion,
    infinityIso] using h
"""
        bodies = {
            'exact_prefix': '',
            'typed_ring_inputs': 'example : True := by\n' + typed + '  exact True.intro\n',
            'typed_ring_square': 'example : True := by\n' + typed + square + '  exact True.intro\n',
            'typed_helper': 'example : True := by\n' + typed + square + helper + '  exact True.intro\n',
            'typed_square_final_wrappers': statement + ' := by\n' + typed + square + helper + wrappers,
            'exact_infinity_inverse_square': declaration + '\n',
        }
    else:
        start = source.index('/-- The old overlap maps into the full punctured order')
        stop = source.index('\ntheorem common_finite ', start)
        prefix = source[:start]
        declaration = source[start:stop]
        partial = '''liftOfAlgHomUnit (k := R) (A := R[X]) (L := Laurent R)
    (B := FiniteOrder R c) (T := OldOverlap R c) (X : R[X])
    (finiteRestriction R c) (oldY R c)'''
        bodies = {
            'exact_prefix': '',
            'original_unit': 'example : (OldOverlap R c)ˣ := oldY R c\n',
            'original_image_equation': '''example :
    finiteRestriction R c (algebraMap R[X] (FiniteOrder R c) X) =
      (oldY R c : OldOverlap R c) := finiteRestriction_X R c
''',
            'partial_unit_wrapper': '#check ' + partial + '\n',
            'complete_unit_wrapper': '#check ' + partial + ' (finiteRestriction_X R c)\n',
            'exact_commonRestriction': declaration + '\n',
        }
    cases = {}
    for name, body in bodies.items():
        sentinel = ('run_cmd do\n  let e ← IO.getStderr\n'
            '  e.putStrLn "GEOMETRY_DIAGNOSTIC ' + name + '"\n  e.flush\n')
        text = prefix + opts + sentinel + body + end
        require('sorry' not in text and 'axiom ' not in text, 'Unproved declaration in probe')
        require('set_option maxRecDepth' not in text, 'Recursion cap changed')
        cases[name] = text
    return cases


def validate(packet, output, hosted=True):
    if hosted:
        require(os.environ.get('GITHUB_ACTIONS') == 'true' and bool(os.environ.get('RUNNER_TEMP')),
                'Hosted Actions only')
    require(packet.name in CONFIG, 'Unexpected packet')
    cfg = CONFIG[packet.name]
    require(sha(packet/'intake.json') == cfg['intake'], 'Frozen intake changed')
    require(sha(packet/'APPLICATION.json') == cfg['application'], 'Frozen application changed')
    intake = json.loads((packet/'intake.json').read_text())
    for name, item in intake['files'].items():
        require(sha(packet/name) == item['sha256'], 'Source binding changed: ' + name)
    result_path = output/'RESULT.json'
    require(result_path.is_file(), 'Mandatory full packet result is missing')
    result = json.loads(result_path.read_text())
    require(result.get('packet') == packet.name and result.get('packet_sha256') == cfg['intake'],
            'Wrong full packet result')
    rows = result.get('commands', [])
    index = intake['order'].index(cfg['module'])
    require([r.get('module') for r in rows] == intake['order'][:index+1],
            'Ordinary check did not reach exactly the observed frontier')
    require(all(r.get('exit_code') == 0 for r in rows[:-1]) and rows[-1].get('exit_code') == 1,
            'Ordinary frontier outcomes changed; reassess instead of probing')
    for name in cfg['imports']:
        require((output/'lib'/(name+'.olean')).is_file(), 'Normally compiled dependency missing: '+name)
    require(runner.original.SECONDS == SECONDS and runner.original.MAX_BYTES == MAX_BYTES,
            'Diagnostic runner caps changed')
    return variants(packet.name, (packet/(cfg['module']+'.lean')).read_text()), sha(result_path)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('packet', choices=list(CONFIG))
    args = parser.parse_args()
    packet = ci.ROOT/'quartics/quartic-318-326/proof/experiments'/args.packet
    output = ci.ROOT/'build/progress-experiments'/args.packet
    cases, result_sha = validate(packet, output)
    env, version = ci.environment(ci.PROJECT, output/'lib')
    logs = output/'scratch-geometry-frontier-diagnostics'
    logs.mkdir(exist_ok=False)
    rows = []
    with tempfile.TemporaryDirectory(prefix='geometry-nonadmitted-', dir=os.environ['RUNNER_TEMP']) as directory:
        root = Path(directory)
        for name, text in cases.items():
            source = root/(name+'.lean')
            source.write_text(text)
            (logs/(name+'.lean.txt')).write_text(text)
            row = runner.bounded_memory(source, root, env, logs/(name+'.log'))
            row['source_sha256'] = hashlib.sha256(text.encode()).hexdigest()
            rows.append(row)
            print(json.dumps(row), flush=True)
    ci.write_json(logs/'DIAGNOSTIC.json', {
        'scope': 'NON_ADMITTED_GEOMETRY_FRONTIER_ISOLATION_ONLY',
        'packet': args.packet, 'packet_intake_sha256': CONFIG[args.packet]['intake'],
        'full_result_sha256': result_sha, 'original_source_sha256': CONFIG[args.packet]['source'],
        'toolchain': version, 'seconds_per_probe': SECONDS, 'bytes_per_probe': MAX_BYTES,
        'variants': rows, 'full_packet_accepted': False, 'baseline_or_experiment_accepted': False,
        'writes_olean': False, 'production_source_changed': False,
    })


if __name__ == '__main__':
    main()
