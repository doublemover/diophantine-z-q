#!/usr/bin/env python3
"""Hosted-only isolated concrete projection and componentwise split tests. No admitted artifacts."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import diagnose_diagonal_identity as previous
ci = previous.ci
PACKET = 'contact-relative-site-descent-r38'
SOURCE_SHA = 'ef83fec2049a0ee80f5e5406ba660b77a49be88d2c37f00624b04ae5a8903f5a'
NAMES = ('split_named','mapped_iso_formula','split_mapIso_projection','split_trans_projection','split_sections_projection','split_path_projection','split_identity_projection','split_sheaf_projection','split_sheaf_arrow','split_mapped_generic','split_mapped_explicit','split_mapped_projection','split_left_formula','split_right_formula','split_sections')

def variants(source):
    for name in NAMES:
        keyword = 'private lemma ' if name not in ('split_sections',) else 'lemma '
        scope = 'set_option profiler true in\nset_option profiler.threshold 0 in\n'
        declaration = source.index(keyword+name+' ')
        start = source.rfind(scope,0,declaration)
        assert start >= 0
        between = source[start+len(scope):declaration]
        assert not between or (between.startswith('/--') and between.rstrip().endswith('-/'))
        positive = ('set_option profiler true in\nset_option profiler.threshold 0 in\n'
            'private theorem diagnostic_positive_'+name+' : True := True.intro\n'
            'run_cmd do\n  let e ← IO.getStderr\n'
            '  e.putStrLn "DIAGONAL positive control before '+name+'"\n  e.flush\n\n')
        source = source[:start]+positive+source[start:]
    scope = 'set_option profiler true in\nset_option profiler.threshold 0 in\n'
    positive = lambda name: scope+'private theorem diagnostic_positive_'+name
    prefix = source[:source.index('\nvariable (R S')]+'\nend OriginalGeometricDiagonal318\n'
    mapped = source[:source.index(positive('split_left_formula'))]+'\nend OriginalGeometricDiagonal318\n'
    left = source[:source.index(positive('split_right_formula'))]+'\nend OriginalGeometricDiagonal318\n'
    result = {'explicit_mapped_signature':mapped,'explicit_left_formula':left,
              'explicit_split_prefix':prefix}
    assert all('sorry' not in text for text in result.values())
    return result

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('packet',choices=[PACKET])
    args=parser.parse_args()
    if os.environ.get('GITHUB_ACTIONS')!='true' or not os.environ.get('RUNNER_TEMP'):
        raise RuntimeError('Hosted GitHub Actions only')
    output=ci.ROOT/'build/progress-experiments'/args.packet
    lib=output/'lib'
    if not all((lib/(n+'.olean')).is_file() for n in
        ('OriginalGeometricTriple318','AffineOverlapDiagonal318')):
        raise RuntimeError('Required normally compiled predecessor is unavailable')
    source=ci.ROOT/'quartics/quartic-318-326/proof/experiments'/args.packet/'OriginalGeometricDiagonal318.lean'
    raw=source.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=SOURCE_SHA:
        raise RuntimeError('Candidate source changed from reviewed bytes')
    env,version=ci.environment(ci.PROJECT,lib)
    logs=output/'scratch-diagonal-explicit-consumer-diagnostics'
    logs.mkdir(exist_ok=False)
    rows=[]
    with tempfile.TemporaryDirectory(prefix='diagonal-explicit-consumers-nonadmitted-',dir=os.environ['RUNNER_TEMP']) as directory:
        root=Path(directory)
        for name,text in variants(raw.decode()).items():
            path=root/(name+'.lean');path.write_text(text)
            row=previous.bounded_memory(path,root,env,logs/(name+'.log'))
            row.update(source_sha256=hashlib.sha256(text.encode()).hexdigest(),contains_sorry=False)
            rows.append(row);print(json.dumps(row),flush=True)
    ci.write_json(logs/'DIAGNOSTIC.json',{'scope':'NON_ADMITTED_DIAGONAL_EXPLICIT_CONSUMERS_SCRATCH_ONLY',
        'source_sha256':SOURCE_SHA,'toolchain':version,'variants':rows,
        'baseline_or_experiment_accepted':False,'writes_olean':False})
if __name__=='__main__':main()
