#!/usr/bin/env python3
"""Hosted-only genuine overlap consumer and isolated conjugation helper probes."""
import argparse
import hashlib
import os
from pathlib import Path
import tempfile
import diagnose_diagonal_identity as previous
ci=previous.ci
PACKET='contact-relative-site-descent-r50'
SOURCE_SHA='f3146ccf5494d5d959621eee8fbc56023e8da1556efb5fd4b1fbd49bae60c15a'
DIAGONAL_SHA='6a3c6fa0d3743425e41035f1eb94335b6807f4d130bddc4dc3582662596345c9'
TRANSPOSE_SHA='cb4722bd1dfa305f5e2864faafd0f0f228d280fa9d5caf097f58842ececf05d6'

def variants(source,consumer):
    assert hashlib.sha256(source.encode()).hexdigest()==SOURCE_SHA
    start=source.index('/-- An actual module-overlap')
    helper=source.index('/-- Opaque categorical transport')
    sheaf=source.index('/-- The actual sheaf overlap square')
    geometric=source.index('lemma geometric_coaction')
    end='\nend OverlapMorphismCoaction318\n'
    header='module\npublic import OverlapMorphismCoaction318\n'
    assert consumer.startswith(header)
    result={'generic_conjugation_only':source[:start]+source[helper:sheaf]+end,
      'actual_module_coaction':source[:helper]+end,
      'actual_sheaf_specialization':source[:geometric]+end,
      'actual_full_geometric_consumer':source,
      'actual_next_descent_consumer':source+'\n'+consumer[len(header):]}
    for text in result.values():
        assert 'sorry' not in text and 'axiom ' not in text
    return result

def main():
    p=argparse.ArgumentParser();p.add_argument('packet',choices=[PACKET]);a=p.parse_args()
    if os.environ.get('GITHUB_ACTIONS')!='true' or not os.environ.get('RUNNER_TEMP'):
        raise RuntimeError('Hosted GitHub Actions only')
    output=ci.ROOT/'build/progress-experiments'/a.packet;lib=output/'lib'
    if not all((lib/(n+'.olean')).is_file() for n in
        ('OriginalGeometricDiagonal318','AffineSplitDiagonalTranspose318','OriginalGeometricAffineLine318')):
        raise RuntimeError('Required genuinely compiled diagonal and actual consumers unavailable')
    packets=ci.ROOT/'quartics/quartic-318-326/proof/experiments';folder=packets/a.packet
    source=(folder/'OverlapMorphismCoaction318.lean').read_text()
    consumer=(folder/'GeometricAffineDescentData318.lean').read_text()
    for name,pin in [('OriginalGeometricDiagonal318',DIAGONAL_SHA),('AffineSplitDiagonalTranspose318',TRANSPOSE_SHA)]:
        assert hashlib.sha256((folder/(name+'.lean')).read_bytes()).hexdigest()==pin
    assert hashlib.sha256(consumer.encode()).hexdigest()=='9325065c2b43cdc8445d10cc8cac6132d7a77621880a8cf642a98126541843cb'
    env,version=ci.environment(ci.PROJECT,lib)
    logs=output/'scratch-overlap-morphism-coherence-diagnostics';logs.mkdir(exist_ok=False)
    rows=[]
    with tempfile.TemporaryDirectory(prefix='overlap-morphism-coherence-nonadmitted-',dir=os.environ['RUNNER_TEMP']) as folder:
        root=Path(folder)
        for name,text in variants(source,consumer).items():
            f=root/(name+'.lean');f.write_text(text)
            row=previous.bounded_memory(f,root,env,logs/(name+'.log'))
            row.update(source_sha256=hashlib.sha256(text.encode()).hexdigest(),contains_sorry=False)
            rows.append(row)
    ci.write_json(logs/'DIAGNOSTIC.json',{'scope':'NON_ADMITTED_GENERIC_HELPER_ACTUAL_SPECIALIZATION_AND_CONSUMERS',
        'source_sha256':SOURCE_SHA,'toolchain':version,'variants':rows,
        'baseline_or_experiment_accepted':False,'writes_olean':False})
if __name__=='__main__':main()
