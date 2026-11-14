#!/usr/bin/env python3
"""Hosted-only NON-ADMITTED exact original-object transport probes.

No production theorem, premise, source, module boundary or limit is changed.
Only the first specimen assumes exact object/comparison/A equalities in scratch.
The assembled specimen proves native A and the same-carrier comparison equality.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import diagnose_picard_overlap_fragments as fragments

isolation = fragments.isolation
ci, runner = fragments.ci, fragments.runner
require, sha = fragments.require, fragments.sha
PACKET, MODULE = fragments.PACKET, fragments.MODULE
SECONDS, MAX_BYTES = fragments.SECONDS, fragments.MAX_BYTES
FRAGMENTS_SCRIPT_SHA = '7ffa5857cba8015bbd0c5cf4f5bc3abc9b298cf977bb7095ce9d0cf4a07c7f90'
NAMES = ['object_transport_with_exact_typed_inputs', 'literal_same_carrier_comparison',
         'assembled_same_carrier_transfer']
EQ_NAME = 'reconstructed_same_carrier_comparison'
ARGS = 'R S L σ hd ht'
E = '(ReconstructedOverlapCompatibility318.comparison '+ARGS+')'
D = '(ReconstructedOverlapCompatibility318.namedComparison '+ARGS+')'
V = '(OriginalGeometricAffineLine318.line '+ARGS+').object'
W = '(tilde (ReconstructedOverlapCompatibility318.descendedModule '+ARGS+'))'
HOBJ = '(ReconstructedOverlapCompatibility318.line_object '+ARGS+')'
HCMP = '(ReconstructedOverlapCompatibility318.comparison_transport '+ARGS+')'
DTYPE = '(Scheme.Modules.pullback (baseMap R S)).obj '+V+' ≅ L.object'
DTYPED = '('+D+' : '+DTYPE+')'
GENERIC = '''
/-- Scratch-only generic same-carrier conjugation, no object-equality eliminator. -/
private lemma conjugation_of_same_carrier_iso_eq {C D : Type*} [Category C] [Category D]
    (P Q : C ⥤ D) {M N : C} (e d : M ≅ N) (he : e = d)
    (a : P.obj M ⟶ Q.obj M) (τ : P.obj N ⟶ Q.obj N)
    (hd : P.map d.inv ≫ a ≫ Q.map d.hom = τ) :
    P.map e.inv ≫ a ≫ Q.map e.hom = τ := by
  cases he
  exact hd
'''


def marker(name):
    return ('\nrun_cmd Lean.Elab.Command.liftIO do\n  let out ← IO.getStderr\n'
            '  out.putStrLn "PICARD_TRANSPORT_'+name+'_COMMAND_END"\n  out.flush\n')


def variants(source):
    prefix, original, statement, native, inner, a, b, prior_assembled = fragments.fragments(source)
    header, conclusion = statement.split(' :\n')
    body = original.split(' := by\n', 1)[1]
    nested = '('+inner+')'
    require(body.count(nested)==1 and body.count(HOBJ)==1 and body.count(HCMP)==1,
            'Original exact transport arguments changed')
    typed_header = header.replace('private lemma reconstructed_actual_overlap',
                                 'private lemma reconstructed_transport_typed_inputs')
    typed_header += ('\n    (hObject : '+V+' = '+W+')\n'
                     '    (hComparison : (Scheme.Modules.pullback (baseMap R S)).mapIso\n'
                     '      (eqToIso hObject) ≪≫ '+D+' = '+E+')\n'
                     '    (hA :\n'+native+')')
    typed_body = body.replace(HOBJ,'hObject').replace(HCMP,'hComparison').replace(nested,'hA')
    typed = typed_header+' :\n'+conclusion+' := by\n'+typed_body
    eq_header = header.replace('private lemma reconstructed_actual_overlap','private lemma '+EQ_NAME)
    eq_decl = (eq_header+' :\n    '+E+' =\n      '+DTYPED+' := by\n'+
               fragments.body_marker('SAME_CARRIER_EQUALITY_ENTER')+
               '  exact ReconstructedOverlapCompatibility318.comparison_eq '+ARGS+'\n'+
               fragments.body_marker('SAME_CARRIER_EQUALITY_EXIT'))
    exact = ('  exact conjugation_of_same_carrier_iso_eq\n'
             '    (Scheme.Modules.pullback (ActualOverlapDiagram318.first (baseMap R S)))\n'
             '    (Scheme.Modules.pullback (ActualOverlapDiagram318.second (baseMap R S)))\n'
             '    '+E+'\n    '+DTYPED+'\n'
             '    ('+EQ_NAME+' '+ARGS+' τ hσ)\n'
             '    (CanonicalSheafOverlap318.actual '+V+' (baseMap R S)) τ\n'
             '    ('+fragments.A_CALL+')\n')
    assembled = statement+' := by\n'+fragments.body_marker('SAME_CARRIER_ASSEMBLED_ENTER')+exact+fragments.body_marker('SAME_CARRIER_ASSEMBLED_EXIT')
    require(assembled.split(' := by\n',1)[0]==statement,'Original helper statement changed')
    texts = [prefix+typed, prefix+eq_decl,
             prefix+GENERIC+marker('AFTER_GENERIC')+a+marker('AFTER_NATIVE_A')+
             eq_decl+marker('AFTER_SAME_CARRIER_EQUALITY')+assembled]
    cases={name:text+marker(name)+isolation.END for name,text in zip(NAMES,texts)}
    for name,text in cases.items():
        require('sorry' not in text and 'axiom ' not in text,'Unexpected placeholder/axiom')
        require(('(hObject :' in text)==(name==NAMES[0]),'Diagnostic object premise escaped')
        require(('(hComparison :' in text)==(name==NAMES[0]),'Diagnostic comparison premise escaped')
        require(('(hA :' in text)==(name==NAMES[0]),'Diagnostic A premise escaped')
        require(isolation.FORBIDDEN_MARKER not in text,'Later production wrapper leaked')
    return cases


def validate(packet,output,hosted=True):
    require(sha(Path(fragments.__file__))==FRAGMENTS_SCRIPT_SHA,'Prior fragment script changed')
    prior_cases,result_sha,log_sha,prior_isolation_sha=fragments.validate(packet,output,hosted=hosted)
    prior=output/'scratch-picard-overlap-fragments';p=prior/'DIAGNOSTIC.json'
    require(p.is_file(),'Mandatory prior fragments result missing');j=json.loads(p.read_text())
    require(j.get('scope')=='NON_ADMITTED_EXACT_PICARD_A_B_ASSEMBLED_ONLY','Wrong prior fragments scope')
    for key,value in [('packet',PACKET),('packet_intake_sha256',isolation.INTAKE_SHA),
                      ('packet_application_sha256',isolation.APPLICATION_SHA),
                      ('original_source_sha256',isolation.SOURCE_SHA),('full_result_sha256',result_sha),
                      ('production_log_sha256',log_sha),('prior_isolation_result_sha256',prior_isolation_sha),
                      ('seconds_per_probe',SECONDS),('bytes_per_probe',MAX_BYTES)]:
        require(j.get(key)==value,'Prior fragment binding changed: '+key)
    for key in ['full_packet_accepted','baseline_or_experiment_accepted','writes_olean',
                'production_source_changed','production_limits_changed']:
        require(j.get(key) is False,'Prior fragment admission/production boundary changed')
    rows=j.get('variants',[])
    require([row.get('variant') for row in rows]==list(prior_cases),'Prior fragment cases changed')
    for index,row in enumerate(rows):
        name=row['variant'];source=prior/(name+'.lean.txt');log=prior/(name+'.log')
        require(source.is_file() and source.read_text()==prior_cases[name],'Prior fragment specimen changed')
        require(sha(source)==row.get('source_sha256') and log.is_file(),'Prior fragment source/log missing')
        require(row.get('admitted') is False and row.get('proof_acceptance') is False,
                'Prior fragment admission detected')
        require(row.get('contains_sorry') is False,'Unexpected prior fragment placeholder')
        require(row.get('exact_A_equation_is_extra_diagnostic_input')==(index==2),
                'Prior fragment premise classification changed')
        text=log.read_text();end='PICARD_FRAGMENT_'+name+'_COMMAND_END'
        if index<2:
            require(row.get('exit_code')==0 and row.get('limit') is None,
                    'Prior control/native-A outcome changed; reassess')
            require(end in text,'Prior completed control/native-A end missing')
        else:
            require(row.get('exit_code')==-9 and row.get('limit')=='SCRATCH_WALL_LIMIT',
                    'Prior transport/assembly outcome changed; reassess')
            body=['PICARD_FRAGMENT_B_BODY_ENTER','PICARD_FRAGMENT_B_BODY_EXIT'] if index==2 else [
                'PICARD_FRAGMENT_ASSEMBLED_AFTER_A_COMMAND_END',
                'PICARD_SITE_BODY_00_ENTER_reconstructed_actual_overlap',
                'PICARD_SITE_BODY_01_EXIT_reconstructed_actual_overlap']
            require(all(x in text for x in body+['SCRATCH_WALL_LIMIT']) and end not in text,
                    'Prior transport/assembly frontier changed')
    return variants((packet/(MODULE+'.lean')).read_text()),result_sha,log_sha,sha(p)


def main():
    parser=argparse.ArgumentParser();parser.add_argument('packet',choices=[PACKET]);args=parser.parse_args()
    packet=ci.ROOT/'quartics/quartic-318-326/proof/experiments'/args.packet
    output=ci.ROOT/'build/progress-experiments'/args.packet
    cases,result_sha,log_sha,prior_sha=validate(packet,output)
    env,version=ci.environment(ci.PROJECT,output/'lib')
    logs=output/'scratch-picard-object-transport';logs.mkdir(exist_ok=False);rows=[]
    with tempfile.TemporaryDirectory(prefix='picard-transport-nonadmitted-',dir=os.environ['RUNNER_TEMP']) as directory:
        root=Path(directory)
        for name,text in cases.items():
            source=root/(name+'.lean');source.write_text(text);(logs/(name+'.lean.txt')).write_text(text)
            row=runner.bounded_memory(source,root,env,logs/(name+'.log'))
            require(not any(p.is_file() and any(p.name.endswith(s) for s in ci.SUFFIXES)
                            for p in root.rglob('*')),'Unexpected compiled scratch artifact')
            row.update(source_sha256=hashlib.sha256(text.encode()).hexdigest(),contains_sorry=False,
                       exact_object_comparison_A_are_extra_diagnostic_inputs=(name==NAMES[0]),
                       admitted=False,proof_acceptance=False)
            rows.append(row);print(json.dumps(row),flush=True)
    ci.write_json(logs/'DIAGNOSTIC.json',{
        'scope':'NON_ADMITTED_EXACT_PICARD_OBJECT_TRANSPORT_ONLY','packet':PACKET,
        'packet_intake_sha256':isolation.INTAKE_SHA,'packet_application_sha256':isolation.APPLICATION_SHA,
        'original_source_sha256':isolation.SOURCE_SHA,'full_result_sha256':result_sha,
        'production_log_sha256':log_sha,'prior_fragments_result_sha256':prior_sha,
        'toolchain':version,'seconds_per_probe':SECONDS,'bytes_per_probe':MAX_BYTES,
        'maximum_additional_scratch_wall_seconds':3*SECONDS,'variants':rows,
        'full_packet_accepted':False,'baseline_or_experiment_accepted':False,'writes_olean':False,
        'production_source_changed':False,'production_limits_changed':False,
        'interpretation':'Compare exact producer-proof substitution against a literal same-carrier comparison and abstract-category conjugation transfer. Only the typed-input probe assumes exact object/comparison/A equalities in scratch. The assembled probe proves both A and its comparison equality, retaining the original helper telescope/conclusion. All processes are nonadmitted; missing timings/frontiers do not uniquely locate kernel, finalization or asynchronous work.'})

if __name__=='__main__':main()
