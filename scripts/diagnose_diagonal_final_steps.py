#!/usr/bin/env python3
"""Hosted-only final diagonal constituent probes. Production Lean bytes are unchanged."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import diagnose_diagonal_identity as previous
ci = previous.ci
PACKET = 'contact-relative-site-descent-r43'
SOURCE_SHA = '8e07961b95723fd439fe62578e433208612ef78fd92e16a395b5b599cf2769aa'
SCOPE = 'set_option profiler true in\nset_option profiler.threshold 0 in\n'
END = '\nend OriginalGeometricDiagonal318\n'

def marker(name):
    return ('\nrun_cmd do\n  let e ← IO.getStderr\n'
        '  e.putStrLn "DIAGONAL final step '+name+'"\n  e.flush\n\n')

def variants(source):
    token = SCOPE+'lemma diagonal_to_split '
    assert source.count(token) == 1
    prefix, final = source.split(token)
    statement, _ = final.split(' := by\n', 1)
    _, target = statement.split(' :\n', 1)
    positive = (SCOPE+'private theorem diagnostic_positive_final_step : True := True.intro\n'
        +marker('positive control'))
    prefix += positive
    split_call = lambda side: (f'split_sections ({side}Map R S S) (diagonal R S)\n'
        f'  (AffineOverlapDiagonal318.diagonal_{side} R S) L')
    probes = {
      'statement': 'private def diagnostic_final_statement : Prop :=\n'+target+'\n',
      'overlap': 'private def diagnostic_overlap := OriginalGeometricTriple318.overlap_map R S L τ\n',
      'pulled': 'private def diagnostic_pulled := AffineSectionConjugation318.pulled_morphism L\n'
        '  (leftMap R S S) (rightMap R S S) (diagonal R S) τ\n',
      'left_split': 'private def diagnostic_left_split := '+split_call('left')+'\n',
      'right_split': 'private def diagnostic_right_split := '+split_call('right')+'\n',
      'mapped_diagonal': '''private lemma diagnostic_mapped_diagonal (hτ : Diagonal R S L τ) :
    (moduleSpecΓFunctor (R := S)).map
      (X := (Scheme.Modules.pullback (Spec.map (diagonal R S))).obj
        ((Scheme.Modules.pullback (Spec.map (leftMap R S S))).obj L.object))
      (Y := L.object)
      ((Scheme.Modules.pullback (Spec.map (diagonal R S))).map τ ≫
        (secondComparison R S L).hom) =
    (moduleSpecΓFunctor (R := S)).map
      (X := (Scheme.Modules.pullback (Spec.map (diagonal R S))).obj
        ((Scheme.Modules.pullback (Spec.map (leftMap R S S))).obj L.object))
      (Y := L.object) (firstComparison R S L).hom :=
  congrArg (fun q :
    (Scheme.Modules.pullback (Spec.map (diagonal R S))).obj
      ((Scheme.Modules.pullback (Spec.map (leftMap R S S))).obj L.object) ⟶ L.object =>
    (moduleSpecΓFunctor (R := S)).map
      (X := (Scheme.Modules.pullback (Spec.map (diagonal R S))).obj
        ((Scheme.Modules.pullback (Spec.map (leftMap R S S))).obj L.object))
      (Y := L.object) q) hτ
''',
      'abstract_cancellation': '''private lemma diagnostic_abstract_cancellation
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} {M N : D} (a : M ≅ F.obj X) (b : N ≅ F.obj Y)
    (t : X ⟶ Y) (r : Y ⟶ Z) (l : X ⟶ Z)
    (m : M ⟶ N) (sr : N ⟶ F.obj Z) (sl : M ⟶ F.obj Z)
    (hm : a.hom ≫ F.map t ≫ b.inv = m)
    (hr : b.hom ≫ F.map r = sr) (hl : a.hom ≫ F.map l = sl)
    (hd : t ≫ r = l) : m ≫ sr = sl := by
  rw [← hm, ← hr]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← F.map_comp, hd]
  exact hl
''',
    }
    result = {
      'clean_split_control': source[:source.index('\nvariable (R S')]+END,
      **{name: prefix+SCOPE+body+marker(name)+END for name,body in probes.items()},
      'explicit_final_control': prefix+token+final,
    }
    for name,text in result.items():
        assert 'sorry' not in text and 'axiom ' not in text
        assert 'lemma split_sections ' in text
        assert '"DIAGONAL after split_sections"' in text
        if name != 'explicit_final_control':
            assert 'lemma diagonal_to_split ' not in text
        if name in probes:
            assert '"DIAGONAL final step '+name+'"' in text
            assert 'diagnostic_positive_final_step :' in text
    return result

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('packet', choices=[PACKET])
    args = parser.parse_args()
    if os.environ.get('GITHUB_ACTIONS') != 'true' or not os.environ.get('RUNNER_TEMP'):
        raise RuntimeError('Hosted GitHub Actions only')
    output = ci.ROOT/'build/progress-experiments'/args.packet
    lib = output/'lib'
    if not all((lib/(n+'.olean')).is_file() for n in
        ('OriginalGeometricTriple318','AffineOverlapDiagonal318')):
        raise RuntimeError('Required normally compiled predecessor is unavailable')
    source = ci.ROOT/'quartics/quartic-318-326/proof/experiments'/args.packet/'OriginalGeometricDiagonal318.lean'
    raw = source.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SOURCE_SHA:
        raise RuntimeError('Candidate source changed from reviewed bytes')
    env,version = ci.environment(ci.PROJECT,lib)
    logs = output/'scratch-diagonal-final-step-diagnostics'
    logs.mkdir(exist_ok=False)
    rows = []
    with tempfile.TemporaryDirectory(prefix='diagonal-final-steps-nonadmitted-',
                                    dir=os.environ['RUNNER_TEMP']) as directory:
        root = Path(directory)
        for name,text in variants(raw.decode()).items():
            path = root/(name+'.lean'); path.write_text(text)
            row = previous.bounded_memory(path,root,env,logs/(name+'.log'))
            row.update(source_sha256=hashlib.sha256(text.encode()).hexdigest(), contains_sorry=False)
            rows.append(row); print(json.dumps(row),flush=True)
    ci.write_json(logs/'DIAGNOSTIC.json', {
        'scope':'NON_ADMITTED_DIAGONAL_FINAL_CONSTITUENTS_ONLY',
        'source_sha256':SOURCE_SHA, 'toolchain':version, 'variants':rows,
        'baseline_or_experiment_accepted':False, 'writes_olean':False})
if __name__ == '__main__': main()
