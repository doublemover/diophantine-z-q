#!/usr/bin/env python3
"""Exact-source hosted core check, separate from the mandatory full packet result."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
# Installed beside the existing checker by the integrator.
import check_progress_experiment as c
PARENT='relative-original-difference-fppf-epimorphism-r2'
CORE='relative-varying-source-word-core-r19'
PARENT_INTAKE='0ea511dd72cbadcdc260bbbf6f5c0e9bbdd1dead6004d42be8fe79f20c0e1903'
PARENT_APPLICATION='f6289e40bf06b2cd8a21411f2f3caea65a098c5ca50266c0035c861071332065'
CORE_INTAKE='c1314ffd95ac73abb6bd8d42b75b67aa1d79a5b5a20444eb54a6bc6851407777'
CORE_APPLICATION='63aa4644ff7d3447c3bf4e75eba99e39693aded6dfc2c71a4c1d00d4c7dc5a57'
CLOSURE_SHA='e719d35ee21490751895da1417e4715041ffae39d54ef0d5b22ddb809a598b63'
TARGETS=['VaryingWordIdealChartClassifier318', 'VaryingNormalizedIdealBaseChange318', 'VaryingWordGlobalFamilyProjection318', 'VaryingWordGlobalClosedQuotient318', 'VaryingBoundedFreeIdealMap318', 'VaryingGlobalFreeQuotientEquiv318', 'VaryingBoundedQuotientRecovery318', 'SchemeClosedOpenPushout318', 'SchemeTwoOpenClosedDescent318', 'AffineClosedRestrictionIso318', 'VaryingLocalFreeQuotientNaturality318', 'VaryingProjectiveQuotientFamily318']
SECONDS=180

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,message):
    if not ok:raise ValueError(message)

def validate(root=c.EXPERIMENTS):
    p=root/PARENT;k=root/CORE
    for path,digest in [(p/'intake.json',PARENT_INTAKE),(p/'APPLICATION.json',PARENT_APPLICATION),
       (k/'intake.json',CORE_INTAKE),(k/'APPLICATION.json',CORE_APPLICATION),(k/'CLOSURE.json',CLOSURE_SHA)]:
        require(sha(path)==digest,'Frozen packet binding changed: '+str(path))
    c.check_application_bindings(p);c.check_application_bindings(k)
    parent=json.loads((p/'intake.json').read_text());core=json.loads((k/'intake.json').read_text());closure=json.loads((k/'CLOSURE.json').read_text())
    require(closure['parent_packet']==PARENT and closure['targets']==TARGETS,'Wrong parent or targets')
    require(closure['parent_intake_sha256']==PARENT_INTAKE and closure['parent_application_sha256']==PARENT_APPLICATION,'Wrong parent contract')
    require(closure['source_changes'] is False and closure['baseline_project_imports']==[],'Unexpected source replacement or baseline shortcut')
    available=set(parent['order']);visited=set();stack=list(TARGETS)
    while stack:
        name=stack.pop()
        if name in visited:continue
        require(name in available,'Unknown target or producer')
        visited.add(name)
        for dep in c.ci.import_names((p/(name+'.lean')).read_text()):
            if dep in available:stack.append(dep)
            else:require(dep.split('.')[0] in c.OFFICIAL_PREFIXES,'Unbound project producer: '+dep)
    order=[n for n in parent['order'] if n in visited]
    require(len(order)==155 and order==core['order']==closure['order'],'Missing, reordered or excess core producer')
    require(set(core['files'])=={n+'.lean' for n in order},'Core file/order mismatch')
    for name in order:
        a=p/(name+'.lean');b=k/(name+'.lean');digest=sha(a)
        require(a.read_bytes()==b.read_bytes(),'Core source differs from full packet: '+name)
        require(digest==parent['files'][name+'.lean']['sha256']==core['files'][name+'.lean']['sha256']==closure['source_sha256'][name],'Core/producer digest mismatch: '+name)
    return order

def command(cache,output):
    return [sys.executable,'-B',str(c.ci.ROOT/'scripts/check_progress_experiment.py'),'check',
        '--packet',CORE,'--cache',str(cache),'--output',str(output),'--seconds',str(SECONDS)]

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--validate-only',action='store_true');a=parser.parse_args()
    order=validate()
    if a.validate_only:
        print(json.dumps({'scope':'EXACT_SOURCE_CLOSURE_STATIC_ONLY','modules':len(order),'targets':TARGETS}));return
    require(os.environ.get('GITHUB_ACTIONS')=='true' and bool(os.environ.get('RUNNER_TEMP')),'Hosted Actions only')
    parent_result=c.ci.ROOT/'build/progress-experiments'/PARENT/'RESULT.json'
    require(parent_result.is_file(),'Full parent check has not produced its own result')
    full=json.loads(parent_result.read_text())
    require(full.get('packet')==PARENT and full.get('packet_sha256')==PARENT_INTAKE,'Full parent result does not match frozen source')
    output=c.ci.ROOT/'build/progress-experiments'/CORE
    cache=c.ci.ROOT/'.cache/progress-ci'
    result=subprocess.run(command(cache,output),cwd=c.ci.PROJECT)
    # Never change the full result, source registry, cache or accepted manifest.
    output.mkdir(parents=True,exist_ok=True)
    (output/'SMOKE_SCOPE.json').write_text(json.dumps({
        'scope':'EXACT_155_MODULE_CORE_ONLY_NOT_FULL_PACKET_ACCEPTANCE',
        'parent':PARENT,'parent_intake_sha256':PARENT_INTAKE,
        'parent_result_sha256':sha(parent_result),'parent_status':full.get('status'),
        'core':CORE,'core_intake_sha256':CORE_INTAKE,'targets':TARGETS,
        'source_modules':155,'same_bytes_as_full_parent':True,'seconds_per_module':SECONDS,
        'standard_checker_exit_code':result.returncode,'full_packet_accepted':False,
        'new_source_acceptance':False,'full_arithmetic_theorem_proved':False},indent=2)+'\n')
    raise SystemExit(result.returncode)
if __name__=='__main__':main()
