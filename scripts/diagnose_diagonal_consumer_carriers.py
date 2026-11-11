#!/usr/bin/env python3
"""Hosted-only unchanged full diagonal and actual consumer normalization probes."""
import argparse
import hashlib
import os
from pathlib import Path
import tempfile
import diagnose_diagonal_identity as previous
ci=previous.ci
PACKET='contact-relative-site-descent-r48'
SOURCE_SHA='6a3c6fa0d3743425e41035f1eb94335b6807f4d130bddc4dc3582662596345c9'
CONSUMER_SHA='cb4722bd1dfa305f5e2864faafd0f0f228d280fa9d5caf097f58842ececf05d6'

def variants(source,consumer,predecessor):
    assert hashlib.sha256(source.encode()).hexdigest()==SOURCE_SHA
    assert hashlib.sha256(consumer.encode()).hexdigest()==CONSUMER_SHA
    assert source==predecessor
    header='module\npublic import OriginalGeometricDiagonal318\n'
    assert consumer.startswith(header)
    terminal='\nrun_cmd do\n  let e ← IO.getStderr\n  e.putStrLn "DIAGONAL actual downstream consumer completed"\n  e.flush\n'
    first=consumer.index('lemma first_transpose')
    second=consumer.index('lemma second_transpose')
    final=consumer.index('/-- The actual geometric diagonal')
    end='\nend AffineSplitDiagonalTranspose318\n'
    result={'unchanged_full_final':source,
      'typed_first_transpose':consumer[:second]+end,
      'typed_second_transpose':consumer[:first]+consumer[second:final]+end,
      'actual_consumer_imported':consumer+terminal,
      'full_final_actual_consumer':source+'\n'+consumer[len(header):]+terminal}
    for text in result.values():
        assert 'sorry' not in text and 'axiom ' not in text
    return result

def main():
    p=argparse.ArgumentParser();p.add_argument('packet',choices=[PACKET]);a=p.parse_args()
    if os.environ.get('GITHUB_ACTIONS')!='true' or not os.environ.get('RUNNER_TEMP'):
        raise RuntimeError('Hosted GitHub Actions only')
    output=ci.ROOT/'build/progress-experiments'/a.packet;lib=output/'lib'
    if not all((lib/(n+'.olean')).is_file() for n in
        ('OriginalGeometricTriple318','AffineOverlapDiagonal318','OriginalGeometricDiagonal318')):
        raise RuntimeError('Required genuinely compiled diagonal/predecessors unavailable')
    packets=ci.ROOT/'quartics/quartic-318-326/proof/experiments'
    source=(packets/a.packet/'OriginalGeometricDiagonal318.lean').read_text()
    consumer=(packets/a.packet/'AffineSplitDiagonalTranspose318.lean').read_text()
    predecessor=(packets/'contact-relative-site-descent-r46'/'OriginalGeometricDiagonal318.lean').read_text()
    env,version=ci.environment(ci.PROJECT,lib)
    logs=output/'scratch-diagonal-consumer-carriers-diagnostics';logs.mkdir(exist_ok=False)
    rows=[]
    with tempfile.TemporaryDirectory(prefix='diagonal-consumer-carriers-nonadmitted-',dir=os.environ['RUNNER_TEMP']) as folder:
        root=Path(folder)
        for name,text in variants(source,consumer,predecessor).items():
            f=root/(name+'.lean');f.write_text(text)
            row=previous.bounded_memory(f,root,env,logs/(name+'.log'))
            row.update(source_sha256=hashlib.sha256(text.encode()).hexdigest(),contains_sorry=False)
            rows.append(row)
    ci.write_json(logs/'DIAGNOSTIC.json',{'scope':'NON_ADMITTED_UNCHANGED_DIAGONAL_AND_ACTUAL_CONSUMER',
        'source_sha256':SOURCE_SHA,'consumer_sha256':CONSUMER_SHA,'toolchain':version,
        'variants':rows,'baseline_or_experiment_accepted':False,'writes_olean':False})
if __name__=='__main__':main()
