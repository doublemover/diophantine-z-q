#!/usr/bin/env python3
"""Hosted-only clean helper, full final, and actual downstream-consumer checks."""
import argparse
import hashlib
import os
from pathlib import Path
import tempfile
import diagnose_diagonal_identity as previous
ci=previous.ci
PACKET='contact-relative-site-descent-r44'
SOURCE_SHA='6da54482393f4d9914cdd18359e0c1d817ac72722d33132c5d2c89e1d5110861'
ORIGINAL_SHA='8e07961b95723fd439fe62578e433208612ef78fd92e16a395b5b599cf2769aa'
CONSUMER_SHA='dbac9fc568620283e935a40259d26f4e19a2b268e029d5267a3051a670efea35'
END='\nend OriginalGeometricDiagonal318\n'

def variants(source,original,consumer):
    assert hashlib.sha256(source.encode()).hexdigest()==SOURCE_SHA
    assert hashlib.sha256(original.encode()).hexdigest()==ORIGINAL_SHA
    assert hashlib.sha256(consumer.encode()).hexdigest()==CONSUMER_SHA
    helper=source.index('set_option profiler true in\nset_option profiler.threshold 0 in\n/-- The final cancellation')
    original_prefix=original[:original.index('\nvariable (R S')]
    assert source[:helper].rstrip()==original_prefix.rstrip()
    statement=lambda text:text.split('lemma diagonal_to_split ',1)[1].split(' := by\n',1)[0]
    assert statement(source)==statement(original)
    consumer_header='module\npublic import OriginalGeometricDiagonal318\n'
    assert consumer.startswith(consumer_header)
    terminal='\nrun_cmd do\n  let e ← IO.getStderr\n  e.putStrLn "DIAGONAL actual downstream consumer completed"\n  e.flush\n'
    result={
      'clean_split_control':original_prefix+END,
      'opaque_helper_only':source[:source.index('\nvariable (R S')]+END,
      'original_final_control':original,
      'opaque_final':source,
      'opaque_final_actual_consumer':source+'\n'+consumer[len(consumer_header):]+terminal,
    }
    for name,text in result.items():
        assert 'sorry' not in text and 'axiom ' not in text
        assert '"DIAGONAL after split_sections"' in text
        if name.startswith('opaque_'):
            assert 'private lemma diagonal_compose ' in text
            assert '"DIAGONAL after diagonal_compose"' in text
        if name not in ('clean_split_control','opaque_helper_only'):
            assert 'lemma diagonal_to_split ' in text
            assert '"DIAGONAL after diagonal_to_split"' in text
    return result

def main():
    p=argparse.ArgumentParser();p.add_argument('packet',choices=[PACKET]);a=p.parse_args()
    if os.environ.get('GITHUB_ACTIONS')!='true' or not os.environ.get('RUNNER_TEMP'):
        raise RuntimeError('Hosted GitHub Actions only')
    output=ci.ROOT/'build/progress-experiments'/a.packet;lib=output/'lib'
    if not all((lib/(n+'.olean')).is_file() for n in ('OriginalGeometricTriple318','AffineOverlapDiagonal318')):
        raise RuntimeError('Required normally compiled predecessors unavailable')
    packets=ci.ROOT/'quartics/quartic-318-326/proof/experiments'
    source=(packets/a.packet/'OriginalGeometricDiagonal318.lean').read_text()
    original=(packets/'contact-relative-site-descent-r43'/'OriginalGeometricDiagonal318.lean').read_text()
    consumer=(packets/a.packet/'AffineSplitDiagonalTranspose318.lean').read_text()
    env,version=ci.environment(ci.PROJECT,lib)
    logs=output/'scratch-diagonal-opaque-final-diagnostics';logs.mkdir(exist_ok=False)
    rows=[]
    with tempfile.TemporaryDirectory(prefix='diagonal-opaque-final-nonadmitted-',dir=os.environ['RUNNER_TEMP']) as folder:
        root=Path(folder)
        for name,text in variants(source,original,consumer).items():
            f=root/(name+'.lean');f.write_text(text)
            row=previous.bounded_memory(f,root,env,logs/(name+'.log'))
            row.update(source_sha256=hashlib.sha256(text.encode()).hexdigest(),contains_sorry=False)
            rows.append(row)
    ci.write_json(logs/'DIAGNOSTIC.json',{'scope':'NON_ADMITTED_OPAQUE_FINAL_AND_ACTUAL_CONSUMER_ONLY',
        'source_sha256':SOURCE_SHA,'original_sha256':ORIGINAL_SHA,'consumer_sha256':CONSUMER_SHA,
        'toolchain':version,'variants':rows,'baseline_or_experiment_accepted':False,'writes_olean':False})
if __name__=='__main__':main()
