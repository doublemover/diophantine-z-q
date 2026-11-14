#!/usr/bin/env python3
"""Hosted-only NON-ADMITTED exact A/B/assembled Picard proof-fragment probes.

B alone has one explicit scratch hypothesis: the exact A equation. It is never
added to production or accepted as the original theorem. The assembled variant
proves A and supplies it to B's original transport term in the SAME process/file.
No production source, original theorem premise or resource limit is changed.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import diagnose_picard_reconstructed_overlap as isolation

ci = isolation.ci
runner = isolation.runner
require = isolation.require
sha = isolation.sha
PACKET = isolation.PACKET
MODULE = isolation.MODULE
SECONDS = isolation.SECONDS
MAX_BYTES = isolation.MAX_BYTES
ISOLATION_SCRIPT_SHA = 'f161cde571f4c3ef51da927fc5de4cb3a52af88cf5c5661e9d1703b929f43b09'
A_NAME = 'reconstructed_native_actual_overlap_fragment'
B_NAME = 'reconstructed_transport_only_fragment'
A_CALL = A_NAME + ' R S L σ hd ht τ hσ'
NAMES = ['exact_prefix_control', 'native_affine_fragment_A',
         'object_transport_fragment_B_with_exact_A_input', 'assembled_same_module_helper']


def body_marker(name):
    return ('  run_tac do\n    let out ← IO.getStderr\n'
            '    out.putStrLn "PICARD_FRAGMENT_' + name + '"\n    out.flush\n')


def end_marker(name):
    return ('\nrun_cmd Lean.Elab.Command.liftIO do\n  let out ← IO.getStderr\n'
            '  out.putStrLn "PICARD_FRAGMENT_' + name + '_COMMAND_END"\n  out.flush\n')


def fragments(source):
    prefix, original, statement = isolation.segments(source)
    require(statement.count(' :\n') == 1, 'Statement conclusion boundary changed')
    header, conclusion = statement.split(' :\n')
    body = original.split(' := by\n', 1)[1]
    start = body.index('    (affine_original_overlap R S\n')
    finish = body.index('\n  run_tac do', start)
    nested = body[start:finish].strip()
    require(nested.startswith('(affine_original_overlap') and nested.endswith('hσ))'),
            'Native A proof boundary changed')
    require(body.count(nested) == 1, 'Native A proof is not unique')
    inner = nested[1:-1]
    old_object = '(OriginalGeometricAffineLine318.line R S L σ hd ht).object'
    require(conclusion.count(old_object) == 1, 'Original object changed')
    require(conclusion.count('ReconstructedOverlapCompatibility318.comparison ') == 2,
            'Original comparison changed')
    native_conclusion = conclusion.replace(old_object,
        '(tilde (ReconstructedOverlapCompatibility318.descendedModule R S L σ hd ht))').replace(
        'ReconstructedOverlapCompatibility318.comparison ',
        'ReconstructedOverlapCompatibility318.namedComparison ')
    a_header = header.replace('private lemma reconstructed_actual_overlap', 'private lemma ' + A_NAME)
    a_decl = (a_header + ' :\n' + native_conclusion + ' := by\n' + body_marker('A_BODY_ENTER') +
              '  exact ' + inner + '\n' + body_marker('A_BODY_EXIT'))
    b_header = header.replace('private lemma reconstructed_actual_overlap', 'private lemma ' + B_NAME)
    b_header += '\n    (hA :\n' + native_conclusion + ')'
    b_body = body.replace(nested, 'hA').replace('PICARD_SITE_BODY_00_ENTER_reconstructed_actual_overlap',
        'PICARD_FRAGMENT_B_BODY_ENTER').replace('PICARD_SITE_BODY_01_EXIT_reconstructed_actual_overlap',
        'PICARD_FRAGMENT_B_BODY_EXIT')
    b_decl = b_header + ' :\n' + conclusion + ' := by\n' + b_body
    assembled = original.replace(nested, '(' + A_CALL + ')')
    require(assembled.replace('(' + A_CALL + ')', nested) == original,
            'Assembled original helper reconstruction failed')
    return prefix, original, statement, native_conclusion, inner, a_decl, b_decl, assembled


def variants(source):
    prefix, original, statement, native, inner, a, b, assembled = fragments(source)
    texts = [prefix, prefix+a, prefix+b,
             prefix+a+end_marker('ASSEMBLED_AFTER_A')+assembled]
    cases = {name: text+end_marker(name)+isolation.END for name, text in zip(NAMES,texts)}
    for name, text in cases.items():
        require('sorry' not in text and 'axiom ' not in text, 'Unexpected placeholder/axiom')
        require(('(hA :' in text) == (name == NAMES[2]), 'Diagnostic premise escaped B')
        require(isolation.FORBIDDEN_MARKER not in text, 'Later production wrapper leaked')
    return cases


def validate(packet, output, hosted=True):
    require(sha(Path(isolation.__file__)) == ISOLATION_SCRIPT_SHA, 'Prior isolation script changed')
    prior_cases, result_sha, log_sha = isolation.validate(packet, output, hosted=hosted)
    prior = output/'scratch-picard-reconstructed-overlap'
    p = prior/'DIAGNOSTIC.json'
    require(p.is_file(), 'Mandatory prior isolation result missing')
    j = json.loads(p.read_text())
    require(j.get('scope') == 'NON_ADMITTED_PICARD_HELPER_ISOLATION_ONLY', 'Wrong isolation scope')
    for key, value in [('packet',PACKET),('packet_intake_sha256',isolation.INTAKE_SHA),
                       ('packet_application_sha256',isolation.APPLICATION_SHA),
                       ('original_source_sha256',isolation.SOURCE_SHA),
                       ('full_result_sha256',result_sha),('production_log_sha256',log_sha),
                       ('seconds_per_probe',SECONDS),('bytes_per_probe',MAX_BYTES)]:
        require(j.get(key) == value, 'Prior isolation binding changed: '+key)
    for key in ['full_packet_accepted','baseline_or_experiment_accepted','writes_olean',
                'production_source_changed','production_limits_changed']:
        require(j.get(key) is False, 'Prior isolation admission/production boundary changed')
    rows = j.get('variants',[])
    require([r.get('variant') for r in rows] == list(prior_cases), 'Prior isolation cases changed')
    for index,row in enumerate(rows):
        name=row['variant']; source=prior/(name+'.lean.txt'); log=prior/(name+'.log')
        require(source.is_file() and source.read_text()==prior_cases[name], 'Prior specimen changed')
        require(sha(source)==row.get('source_sha256') and log.is_file(), 'Prior specimen/log missing')
        require(row.get('admitted') is False and row.get('proof_acceptance') is False,
                'Prior scratch admission detected')
        require(row.get('contains_sorry') == (index==1), 'Prior placeholder classification changed')
        if index<2:
            require(row.get('exit_code')==0 and row.get('limit') is None,
                    'Prior prefix/statement outcome changed; reassess')
            require('PICARD_NONADMITTED_'+name+'_COMMAND_END' in log.read_text(),
                    'Prior completed control marker missing')
        else:
            require(row.get('exit_code')==-9 and row.get('limit')=='SCRATCH_WALL_LIMIT',
                    'Prior genuine-helper outcome changed; reassess')
            text=log.read_text()
            require(all(s in text for s in ['PICARD_SITE_BODY_00_ENTER_reconstructed_actual_overlap',
                    'PICARD_SITE_BODY_01_EXIT_reconstructed_actual_overlap','SCRATCH_WALL_LIMIT']),
                    'Prior genuine-helper boundary changed')
            require('PICARD_NONADMITTED_'+name+'_COMMAND_END' not in text,
                    'Prior helper end frontier changed')
    return variants((packet/(MODULE+'.lean')).read_text()),result_sha,log_sha,sha(p)


def main():
    parser=argparse.ArgumentParser();parser.add_argument('packet',choices=[PACKET]);args=parser.parse_args()
    packet=ci.ROOT/'quartics/quartic-318-326/proof/experiments'/args.packet
    output=ci.ROOT/'build/progress-experiments'/args.packet
    cases,result_sha,log_sha,prior_sha=validate(packet,output)
    env,version=ci.environment(ci.PROJECT,output/'lib')
    logs=output/'scratch-picard-overlap-fragments';logs.mkdir(exist_ok=False)
    rows=[]
    with tempfile.TemporaryDirectory(prefix='picard-fragments-nonadmitted-',dir=os.environ['RUNNER_TEMP']) as directory:
        root=Path(directory)
        for name,text in cases.items():
            source=root/(name+'.lean');source.write_text(text);(logs/(name+'.lean.txt')).write_text(text)
            row=runner.bounded_memory(source,root,env,logs/(name+'.log'))
            require(not any(p.is_file() and any(p.name.endswith(s) for s in ci.SUFFIXES)
                            for p in root.rglob('*')), 'Unexpected compiled scratch artifact')
            row.update(source_sha256=hashlib.sha256(text.encode()).hexdigest(),contains_sorry=False,
                       exact_A_equation_is_extra_diagnostic_input=(name==NAMES[2]),
                       admitted=False,proof_acceptance=False)
            rows.append(row);print(json.dumps(row),flush=True)
    parts=fragments((packet/(MODULE+'.lean')).read_text())
    ci.write_json(logs/'DIAGNOSTIC.json',{
        'scope':'NON_ADMITTED_EXACT_PICARD_A_B_ASSEMBLED_ONLY','packet':PACKET,
        'packet_intake_sha256':isolation.INTAKE_SHA,'packet_application_sha256':isolation.APPLICATION_SHA,
        'original_source_sha256':isolation.SOURCE_SHA,'full_result_sha256':result_sha,
        'production_log_sha256':log_sha,'prior_isolation_result_sha256':prior_sha,
        'fragment_sha256':{n:hashlib.sha256(t.encode()).hexdigest() for n,t in zip(
            ['prefix','original_helper','original_statement','exact_native_A_conclusion','exact_native_A_term',
             'native_A_declaration','transport_B_declaration','assembled_original_helper'],parts)},
        'toolchain':version,'seconds_per_probe':SECONDS,'bytes_per_probe':MAX_BYTES,
        'maximum_additional_scratch_wall_seconds':4*SECONDS,'variants':rows,
        'full_packet_accepted':False,'baseline_or_experiment_accepted':False,'writes_olean':False,
        'production_source_changed':False,'production_limits_changed':False,
        'interpretation':'Independent process outcomes isolate native affine compatibility A and original object-equality transport B. B assumes exactly A only in scratch, never in production. The assembled same-module variant proves A and supplies its opaque theorem to the original unchanged helper statement; it is not an admitted proof or production pass. Missing markers/timings do not uniquely locate kernel, finalization or asynchronous work.'})

if __name__=='__main__':main()
