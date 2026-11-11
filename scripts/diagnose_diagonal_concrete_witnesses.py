#!/usr/bin/env python3
"""Hosted-only typed concrete witness, full final, and actual consumer probes."""
import argparse
import hashlib
import os
from pathlib import Path
import tempfile
import diagnose_diagonal_identity as previous
ci=previous.ci
PACKET='contact-relative-site-descent-r45'
SOURCE_SHA='365ee8534e364f88f57eee603a67ebb9d7b531d81865e2f5698adf318177b018'
PREDECESSOR_SHA='6da54482393f4d9914cdd18359e0c1d817ac72722d33132c5d2c89e1d5110861'
CONSUMER_SHA='dbac9fc568620283e935a40259d26f4e19a2b268e029d5267a3051a670efea35'
END='\nend OriginalGeometricDiagonal318\n'
SCOPE='set_option profiler true in\nset_option profiler.threshold 0 in\n'
WITNESSES=('concrete_overlap','concrete_pulled','concrete_right_split','concrete_left_split')

def variants(source,predecessor,consumer):
    assert hashlib.sha256(source.encode()).hexdigest()==SOURCE_SHA
    assert hashlib.sha256(predecessor.encode()).hexdigest()==PREDECESSOR_SHA
    assert hashlib.sha256(consumer.encode()).hexdigest()==CONSUMER_SHA
    statement=lambda text:text.split('lemma diagonal_to_split ',1)[1].split(' := by\n',1)[0]
    assert statement(source)==statement(predecessor)
    added='/-- Named concrete comparison carriers'
    assert source[:source.index(added)]==predecessor[:predecessor.index(SCOPE+'lemma diagonal_to_split ')]
    prefix=source[:source.index(SCOPE+'private lemma concrete_overlap ')]
    fragments={}
    for i,name in enumerate(WITNESSES):
        start=source.index(SCOPE+'private lemma '+name+' ')
        stop=source.index(SCOPE+('private lemma '+WITNESSES[i+1]+' ' if i+1<len(WITNESSES) else 'lemma diagonal_to_split '))
        fragments[name]=source[start:stop]
        assert ' :\n' in fragments[name] and ' :=\n' in fragments[name]
    header='module\npublic import OriginalGeometricDiagonal318\n'
    assert consumer.startswith(header)
    terminal='\nrun_cmd do\n  let e ← IO.getStderr\n  e.putStrLn "DIAGONAL actual downstream consumer completed"\n  e.flush\n'
    result={
      'clean_split_control':predecessor[:predecessor.index(SCOPE+'/-- The final cancellation')]+END,
      **{name:prefix+fragments[name]+END for name in WITNESSES},
      'all_concrete_witnesses':source[:source.index(SCOPE+'lemma diagonal_to_split ')]+END,
      'concrete_final':source,
      'concrete_final_actual_consumer':source+'\n'+consumer[len(header):]+terminal,
    }
    for name,text in result.items():
        assert 'sorry' not in text and 'axiom ' not in text
        assert '"DIAGONAL after split_sections"' in text
        if name.startswith('concrete_final'):
            assert 'lemma diagonal_to_split ' in text
            assert all('private lemma '+w+' ' in text for w in WITNESSES)
        else:
            assert 'lemma diagonal_to_split ' not in text
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
    predecessor=(packets/'contact-relative-site-descent-r44'/'OriginalGeometricDiagonal318.lean').read_text()
    consumer=(packets/a.packet/'AffineSplitDiagonalTranspose318.lean').read_text()
    env,version=ci.environment(ci.PROJECT,lib)
    logs=output/'scratch-diagonal-concrete-witness-diagnostics';logs.mkdir(exist_ok=False)
    rows=[]
    with tempfile.TemporaryDirectory(prefix='diagonal-concrete-witness-nonadmitted-',dir=os.environ['RUNNER_TEMP']) as folder:
        root=Path(folder)
        for name,text in variants(source,predecessor,consumer).items():
            f=root/(name+'.lean');f.write_text(text)
            row=previous.bounded_memory(f,root,env,logs/(name+'.log'))
            row.update(source_sha256=hashlib.sha256(text.encode()).hexdigest(),contains_sorry=False)
            rows.append(row)
    ci.write_json(logs/'DIAGNOSTIC.json',{'scope':'NON_ADMITTED_TYPED_CONCRETE_WITNESSES_FINAL_AND_CONSUMER',
        'source_sha256':SOURCE_SHA,'predecessor_sha256':PREDECESSOR_SHA,'consumer_sha256':CONSUMER_SHA,
        'toolchain':version,'variants':rows,'baseline_or_experiment_accepted':False,'writes_olean':False})
if __name__=='__main__':main()
