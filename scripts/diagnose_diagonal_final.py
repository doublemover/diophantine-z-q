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
PACKET = 'contact-relative-site-descent-r42'
SOURCE_SHA = '8e07961b95723fd439fe62578e433208612ef78fd92e16a395b5b599cf2769aa'
ORIGINAL_SHA = '01c9d643bdb3b91a155cfac8cee6d14d42a29dfd54babc3da14879fa3d34910e'
def variants(source):
    original=(ci.ROOT/'quartics/quartic-318-326/proof/experiments/contact-relative-site-descent-r41/OriginalGeometricDiagonal318.lean').read_text()
    assert hashlib.sha256(original.encode()).hexdigest()==ORIGINAL_SHA
    scope='set_option profiler true in\nset_option profiler.threshold 0 in\n'
    token=scope+'lemma diagonal_to_split '
    assert source.split(token)[0]==original.split(token)[0]
    positive=scope+'private theorem diagnostic_positive_final : True := True.intro\nrun_cmd do\n  let e ← IO.getStderr\n  e.putStrLn "DIAGONAL positive control before final"\n  e.flush\n\n'
    result={
      'clean_split_control':source[:source.index('\nvariable (R S')]+ '\nend OriginalGeometricDiagonal318\n',
      'original_final':original.replace(token,positive+token),
      'explicit_final':source.replace(token,positive+token),
    }
    for key,text in result.items():
        assert 'sorry' not in text
        assert 'lemma split_sections ' in text and '"DIAGONAL after split_sections"' in text
        if key!='clean_split_control':
            assert 'lemma diagonal_to_split ' in text
            assert '"DIAGONAL after diagonal_to_split"' in text
            assert 'diagnostic_positive_final :' in text
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
    logs=output/'scratch-diagonal-final-diagnostics'
    logs.mkdir(exist_ok=False)
    rows=[]
    with tempfile.TemporaryDirectory(prefix='diagonal-final-nonadmitted-',dir=os.environ['RUNNER_TEMP']) as directory:
        root=Path(directory)
        for name,text in variants(raw.decode()).items():
            path=root/(name+'.lean');path.write_text(text)
            row=previous.bounded_memory(path,root,env,logs/(name+'.log'))
            row.update(source_sha256=hashlib.sha256(text.encode()).hexdigest(),contains_sorry=False)
            rows.append(row);print(json.dumps(row),flush=True)
    ci.write_json(logs/'DIAGNOSTIC.json',{'scope':'NON_ADMITTED_DIAGONAL_FINAL_SCRATCH_ONLY',
        'source_sha256':SOURCE_SHA,'toolchain':version,'variants':rows,
        'baseline_or_experiment_accepted':False,'writes_olean':False})
if __name__=='__main__':main()
