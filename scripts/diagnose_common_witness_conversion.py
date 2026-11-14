#!/usr/bin/env python3
"""Hosted-only exact Common witness-conversion probes; no production repair/admission."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import diagnose_diagonal_identity as runner
ci=runner.ci
PACKET='height-original-ks-lattice-assembly-r16'
MODULE='IntegralOriginalCommonRestriction318'
SOURCE_SHA='11d365488de375da288b7c3336d34e80f46213393fce57a57373b86ca8df6963'
INTAKE_SHA='af1f9b005979d4b1ba85de7fa6de951f1c5e051ced68437dabd2b2968a13a0ae'
APPLICATION_SHA='e50442742b6ab98a636de02e2d3b4acc0bb77d2cbb8e00ea4b0d749331772272'
SECONDS=90
MAX_BYTES=2*1024*1024
EXPECTED_FLAGS=("-j1", "-M", "6144", "-Ddebug.skipKernelTC=false")
COMPILED_SUFFIXES=(".olean", ".ilean", ".ir")

def require(ok,message):
    if not ok:raise ValueError(message)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def require_no_compiled_artifacts(root,module=None):
    unexpected=sorted(str(p.relative_to(root)) for suffix in COMPILED_SUFFIXES
        for p in root.rglob((module or "*")+suffix))
    require(not unexpected,"Unexpected compiled artifacts: "+", ".join(unexpected))

def variants(source):
    require(hashlib.sha256(source.encode()).hexdigest()==SOURCE_SHA,'Frozen source changed')
    start=source.index('/-- The old overlap maps into the full punctured order')
    stop=source.index('\ntheorem common_finite ',start)
    prefix=source[:start];declaration=source[start:stop]
    partial='''liftOfAlgHomUnit (k := R) (A := R[X]) (L := Laurent R)
    (B := FiniteOrder R c) (T := OldOverlap R c) (X : R[X])
    (finiteRestriction R c) (oldY R c)'''
    typed='''example :
    finiteRestriction R c (algebraMap R[X] (FiniteOrder R c) X) =
      (oldY R c : OldOverlap R c) := finiteRestriction_X R c
'''
    local_lift='example : True := by\n  let lift := '+partial+'\n'
    change_witness='''  have completed := lift (by
    change finiteRestriction R c (algebraMap R[X] (FiniteOrder R c) X) =
      (oldY R c : OldOverlap R c)
    exact finiteRestriction_X R c)
  exact True.intro
'''
    coe_witness='''  have hX : finiteRestriction R c (algebraMap R[X] (FiniteOrder R c) X) =
      (oldY R c : OldOverlap R c) := finiteRestriction_X R c
  have completed := lift (by
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hX)
  exact True.intro
'''
    bodies={
        'exact_prefix':'',
        'explicit_equations':'set_option pp.explicit true\nset_option pp.universes true\n#check finiteRestriction_X R c\n#check '+partial+'\n',
        'typed_original_equation':typed,
        'exact_staged_definition':declaration+'\n',
        'literal_expected_witness':local_lift+change_witness,
        'normalized_coercion_witness':local_lift+coe_witness,
    }
    options='\nset_option diagnostics true\nset_option profiler true\nset_option profiler.threshold 0\nset_option stderrAsMessages false\n'
    result={}
    for name,body in bodies.items():
        marker='run_cmd do\n  let e ← IO.getStderr\n  e.putStrLn "COMMON_WITNESS_DIAGNOSTIC '+name+'"\n  e.flush\n'
        text=prefix+options+marker+body+'\nend IntegralOriginalCommonRestriction318\n'
        require('sorry' not in text and 'axiom ' not in text,'Unproved declaration')
        require('set_option maxRecDepth' not in text,'Recursion limit changed')
        result[name]=text
    return result

def validate(packet,output,hosted=True):
    if hosted:require(os.environ.get('GITHUB_ACTIONS')=='true' and bool(os.environ.get('RUNNER_TEMP')),'Hosted Actions only')
    require(tuple(ci.FLAGS)==EXPECTED_FLAGS,'Strict compiler flags changed')
    require(packet.name==PACKET,'Wrong packet')
    require(sha(packet/'intake.json')==INTAKE_SHA and sha(packet/'APPLICATION.json')==APPLICATION_SHA,'Frozen packet changed')
    intake=json.loads((packet/'intake.json').read_text())
    for name,item in intake['files'].items():require(sha(packet/name)==item['sha256'],'Source binding changed: '+name)
    rp=output/'RESULT.json';require(rp.is_file(),'Mandatory full result missing');r=json.loads(rp.read_text())
    require(r.get('packet')==PACKET and r.get('packet_sha256')==INTAKE_SHA,'Wrong full result')
    rows=r.get('commands',[]);idx=intake['order'].index(MODULE)
    require([x.get('module') for x in rows]==intake['order'][:idx+1],'Ordinary frontier changed')
    require(all(x.get('exit_code')==0 for x in rows[:-1]) and rows[-1].get('exit_code')==1,'Ordinary outcomes changed')
    require_no_compiled_artifacts(output/'lib',MODULE)
    require((output/'lib/LocalizedTensorRestriction318.olean').is_file(),'Compiled dependency missing')
    require(runner.original.SECONDS==SECONDS and runner.original.MAX_BYTES==MAX_BYTES,'Runner caps changed')
    return variants((packet/(MODULE+'.lean')).read_text()),sha(rp)

def main():
    p=argparse.ArgumentParser();p.add_argument('packet',choices=[PACKET]);a=p.parse_args()
    packet=ci.ROOT/'quartics/quartic-318-326/proof/experiments'/a.packet
    output=ci.ROOT/'build/progress-experiments'/a.packet
    cases,result_sha=validate(packet,output);env,version=ci.environment(ci.PROJECT,output/'lib')
    logs=output/'scratch-common-witness-diagnostics';logs.mkdir(exist_ok=False);rows=[]
    with tempfile.TemporaryDirectory(prefix='common-witness-nonadmitted-',dir=os.environ['RUNNER_TEMP']) as t:
        root=Path(t)
        for name,text in cases.items():
            source=root/(name+'.lean');source.write_text(text);(logs/(name+'.lean.txt')).write_text(text)
            row=runner.bounded_memory(source,root,env,logs/(name+'.log'))
            require_no_compiled_artifacts(root)
            row['source_sha256']=hashlib.sha256(text.encode()).hexdigest();rows.append(row);print(json.dumps(row),flush=True)
        require_no_compiled_artifacts(root)
        require_no_compiled_artifacts(output/'lib',MODULE)
    ci.write_json(logs/'DIAGNOSTIC.json',{'scope':'NON_ADMITTED_COMMON_WITNESS_CONVERSION_ONLY','packet':PACKET,'packet_intake_sha256':INTAKE_SHA,'original_source_sha256':SOURCE_SHA,'full_result_sha256':result_sha,'toolchain':version,'seconds_per_probe':SECONDS,'probe_wall_cap_sum_seconds':len(cases)*SECONDS,'aggregate_runtime_note':'Up to 540 seconds of probe wall caps plus setup/cleanup, separate from normal production cap','strict_flags':list(EXPECTED_FLAGS),'compiled_artifact_absence_checked':True,'bytes_per_probe':MAX_BYTES,'variants':rows,'full_packet_accepted':False,'baseline_or_experiment_accepted':False,'writes_olean':False,'production_source_changed':False})
if __name__=='__main__':main()
