#!/usr/bin/env python3
"""Hosted-only concrete dictionary conversion probes, never production admission."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import diagnose_common_expression_boundary as previous
witness = previous.previous
ci = witness.ci
DEPENDENCY_SHA = '238aadd6e994693b8297fd4434a2841d4f44fde789028dcfd3f64b4435ed2e30'
NORMALIZERS = {
    'restricted_dictionary_dsimp': """    have hX := finiteRestriction_X R c
    dsimp only [oldOverlapCommRing, CommRing.toCommSemiring,
      CommSemiring.toSemiring, Algebra.TensorProduct.instCommRing,
      Algebra.TensorProduct.instRing] at hX ⊢
    exact hX""",
    'instance_transparency_witness': """    with_reducible_and_instances
      exact finiteRestriction_X R c""",
}

def check_dependencies():
    witness.require(witness.sha(Path(previous.__file__)) == DEPENDENCY_SHA,
        'Pinned structural diagnostic changed')
    previous.check_dependencies()

def variants(source):
    # This guard/prefix comes from the exact current r16 diagnostic, not a guessed substring.
    original = witness.variants(source)
    prefix = original['exact_prefix']
    end = '\nend IntegralOriginalCommonRestriction318\n'
    witness.require(prefix.endswith(end), 'Namespace suffix changed')
    body = """example : True := by
  let lift := liftOfAlgHomUnit (k := R) (A := R[X]) (L := Laurent R)
    (B := FiniteOrder R c) (T := OldOverlap R c) (X : R[X])
    (finiteRestriction R c) (oldY R c)
  have completed := lift (by
NORMALIZER)
  exact True.intro
"""
    cases = {}
    for name, normalizer in NORMALIZERS.items():
        marker = ('run_cmd do\n  let e ← IO.getStderr\n'
                  '  e.putStrLn "COMMON_DICTIONARY ' + name + '"\n  e.flush\n')
        text = prefix[:-len(end)] + marker + body.replace('NORMALIZER', normalizer) + end
        witness.require('sorry' not in text and 'axiom ' not in text, 'Unproved specimen')
        witness.require('set_option maxRecDepth' not in text, 'Recursion budget changed')
        cases[name] = text
    return cases

def validate(packet, output, hosted=True):
    check_dependencies()
    _, result_sha = witness.validate(packet, output, hosted)
    return variants((packet / (witness.MODULE + '.lean')).read_text()), result_sha

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('packet', choices=[witness.PACKET])
    args = parser.parse_args()
    packet = ci.ROOT / 'quartics/quartic-318-326/proof/experiments' / args.packet
    output = ci.ROOT / 'build/progress-experiments' / args.packet
    cases, result_sha = validate(packet, output)
    env, version = ci.environment(ci.PROJECT, output / 'lib')
    # Reuse the existing uploaded phase directory and replace its old two probes,
    # never append another diagnostic invocation to this lane.
    logs = output / 'scratch-common-expression-diagnostics'
    logs.mkdir(exist_ok=False)
    rows = []
    with tempfile.TemporaryDirectory(prefix='common-dictionary-nonadmitted-', dir=os.environ['RUNNER_TEMP']) as temp:
        root = Path(temp)
        for name, text in cases.items():
            source = root / (name + '.lean')
            source.write_text(text)
            (logs / (name + '.lean.txt')).write_text(text)
            row = witness.runner.bounded_memory(source, root, env, logs / (name + '.log'))
            witness.require_no_compiled_artifacts(root)
            row['source_sha256'] = hashlib.sha256(text.encode()).hexdigest()
            rows.append(row)
            print(json.dumps(row), flush=True)
        witness.require_no_compiled_artifacts(root)
        witness.require_no_compiled_artifacts(output / 'lib', witness.MODULE)
    ci.write_json(logs / 'DIAGNOSTIC.json', {
        'scope': 'NON_ADMITTED_COMMON_DICTIONARY_CONVERSION_ONLY',
        'packet': witness.PACKET, 'packet_intake_sha256': witness.INTAKE_SHA,
        'original_source_sha256': witness.SOURCE_SHA, 'full_result_sha256': result_sha,
        'toolchain': version, 'seconds_per_probe': witness.SECONDS,
        'bytes_per_probe': witness.MAX_BYTES,
        'probe_wall_cap_sum_seconds': len(cases) * witness.SECONDS,
        'aggregate_runtime_note': 'Replaces the previous two structural probes; unchanged 180 seconds probe wall caps plus setup/cleanup, separate from production cap.',
        'strict_flags': list(witness.EXPECTED_FLAGS),
        'compiled_artifact_absence_checked': True, 'variants': rows,
        'verification_boundary': 'A successful True endpoint means this specialized lift term elaborated; not full commonRestriction, downstream theorem, recursive audit, or production acceptance.',
        'full_packet_accepted': False, 'baseline_or_experiment_accepted': False,
        'writes_olean': False, 'production_source_changed': False,
    })
if __name__ == '__main__':
    main()
