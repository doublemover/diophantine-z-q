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
PACKET = 'contact-relative-site-descent-r41'
SOURCE_SHA = '01c9d643bdb3b91a155cfac8cee6d14d42a29dfd54babc3da14879fa3d34910e'
NAMES = ('split_named','mapped_iso_formula','split_mapIso_projection','split_trans_projection','split_sections_projection','split_path_projection','split_identity_projection','split_sheaf_projection','split_sheaf_arrow','split_mapped_generic','split_mapped_explicit','split_mapped_projection','split_left_formula','split_right_formula','counit_composition','sections_composition_actual','sections_composition_generic','split_composition_explicit','split_identity_explicit','split_sections')

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
    # The terminal colon is essential: split_sections must NOT match
    # split_sections_projection (the invalid r39 identity control).
    positive = lambda name: scope+'private theorem diagnostic_positive_'+name+' :'
    end = '\nend OriginalGeometricDiagonal318\n'
    abstract_start=source.index(positive('counit_composition'))
    actual_start=source.index(positive('sections_composition_actual'))
    generic_start=source.index(positive('sections_composition_generic'))
    composition_start=source.index(positive('split_composition_explicit'))
    identity_start=source.index(positive('split_identity_explicit'))
    split_start=source.index(positive('split_sections'))
    result = {
      'abstract_counit': source[:actual_start]+end,
      'actual_composition': source[:generic_start]+end,
      'generic_composition': source[:composition_start]+end,
      'concrete_composition': source[:identity_start]+end,
      # Standalone identity, not blocked by either composition bridge.
      'identity_isolated': source[:abstract_start]+source[identity_start:split_start]+end,
      'clean_split': source[:source.index('\nvariable (R S')]+end,
    }
    required={
      'abstract_counit':['counit_composition'],
      'actual_composition':['counit_composition','sections_composition_actual'],
      'generic_composition':['sections_composition_generic'],
      'concrete_composition':['counit_composition','sections_composition_actual','sections_composition_generic','split_composition_explicit'],
      'identity_isolated':['split_identity_explicit'],
      'clean_split':['counit_composition','sections_composition_actual','sections_composition_generic','split_composition_explicit','split_identity_explicit','split_sections'],
    }
    for key,text in result.items():
        assert 'sorry' not in text and 'lemma diagonal_to_split' not in text
        for name in required[key]:
            assert ('lemma '+name+' ') in text, (key,name,'declaration missing')
            assert ('"DIAGONAL after '+name+'"') in text, (key,name,'terminal marker missing')
    assert 'lemma counit_composition ' not in result['identity_isolated']
    assert 'lemma sections_composition_actual ' not in result['identity_isolated']
    assert 'lemma sections_composition_generic ' not in result['identity_isolated']
    assert 'lemma split_composition_explicit ' not in result['identity_isolated']
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
    logs=output/'scratch-diagonal-counit-diagnostics'
    logs.mkdir(exist_ok=False)
    rows=[]
    with tempfile.TemporaryDirectory(prefix='diagonal-counit-nonadmitted-',dir=os.environ['RUNNER_TEMP']) as directory:
        root=Path(directory)
        for name,text in variants(raw.decode()).items():
            path=root/(name+'.lean');path.write_text(text)
            row=previous.bounded_memory(path,root,env,logs/(name+'.log'))
            row.update(source_sha256=hashlib.sha256(text.encode()).hexdigest(),contains_sorry=False)
            rows.append(row);print(json.dumps(row),flush=True)
    ci.write_json(logs/'DIAGNOSTIC.json',{'scope':'NON_ADMITTED_DIAGONAL_COUNIT_SCRATCH_ONLY',
        'source_sha256':SOURCE_SHA,'toolchain':version,'variants':rows,
        'baseline_or_experiment_accepted':False,'writes_olean':False})
if __name__=='__main__':main()
