#!/usr/bin/env python3
"""Bounded first-time checks of isolated drafts against verified baseline artifacts.

No experiment is added to the accepted progress manifest or its artifact cache.
A successful packet check is not independent source acceptance or a whole rebuild.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import time
import check_progress_lean as ci
from check_lean import code_only

EXPERIMENTS = ci.ROOT / 'quartics/quartic-318-326/proof/experiments'
OFFICIAL_PREFIXES = {'Mathlib','Lean','Std','Init','Batteries','Qq','Aesop','Plausible','ProofWidgets','ImportGraph'}


def packet(name, baseline, root=EXPERIMENTS):
    if not re.fullmatch(r'[a-z][a-z0-9-]*', name):
        raise ValueError('Invalid packet name')
    folder = root / name
    data = json.loads((folder/'intake.json').read_text())
    order = data['order']
    if not order or len(order) != len(set(order)):
        raise ValueError('Empty or duplicate packet order')
    if set(data['files']) != {n+'.lean' for n in order}:
        raise ValueError('Packet file/order mismatch')
    seen, direct, external = set(), set(), set()
    for n in order:
        if (not re.fullmatch(r'[A-Za-z_]\w*',n) or n in baseline['module_keys']
                or n in OFFICIAL_PREFIXES or n in {'ExperimentAudit','CheckpointAudit'}):
            raise ValueError('Invalid or shadowing module name')
        source = folder/(n+'.lean'); row = data['files'][n+'.lean']
        if ci.sha(source) != row['sha256']: raise ValueError('Draft source hash mismatch: '+n)
        code = code_only(source.read_text())
        if re.search(r'\b(sorry|admit|native_decide|axiom|unsafe|implemented_by|constant)\b',code):
            raise ValueError('Unproved axiom, placeholder or native evaluator in '+n)
        if re.search(r'\b(?:debug\.)?skipKernelTC\b',code):
            raise ValueError('Draft cannot change kernel checking')
        imports = ci.import_names(source.read_text())
        if imports != set(row['imports']): raise ValueError('Declared imports mismatch: '+n)
        for dep in imports:
            if dep in seen: continue
            if dep in baseline['module_keys']: direct.add(dep)
            elif dep.split('.')[0] in OFFICIAL_PREFIXES: external.add(dep)
            else: raise ValueError('Unknown or nonpreceding import: '+dep)
        seen.add(n)
    return folder,data,direct,external


def required_baseline(plan,direct):
    needed=set()
    def visit(n):
        if n in needed:return
        for d in plan['dependencies'][n]:visit(d)
        needed.add(n)
    for n in direct:visit(n)
    return [n for n in plan['module_order'] if n in needed]


def restore_baseline(cache, lib, plan, needed):
    old=json.loads((cache/'receipt.json').read_text())
    if any(old.get(k)!=v for k,v in {'schema':ci.SCHEMA,'status':'PASS','base':plan['base'],
            'scope':'Complete source coverage and recursive axiom audit'}.items()):
        raise ValueError('A verified full baseline cache is required; run Progress Lean cohorts first')
    built={}
    for n in needed:
        entry=old.get('modules',{}).get(n)
        if not ci.reusable(entry,n,plan,cache/'lib',built):
            raise ValueError('Missing, stale or corrupt baseline artifact: '+n)
        ci.copy_artifacts(cache/'lib',lib,n,entry['files']);built[n]=entry
    return built


def audit_text(order):
    # Enumerate private/generated declarations as in the accepted snapshot audit.
    return ('module\n'+''.join('import all '+n+'\n' for n in order)+
      'import Lean.Util.CollectAxioms\n\nset_option maxHeartbeats 0\n'+
      'open Lean Elab Command in\nrun_cmd do\n  let env ← getEnv\n'+
      '  let modules : Array Name := #['+','.join('`'+n for n in order)+']\n'+
      '''  let mut count : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        count := count+1
  unless found == modules.size do throwError "Missing imported modules: {found}/{modules.size}"
  logInfo m!"EXPERIMENT_AUDIT_PASS declarations={count} modules={found}"
''')


def compile_bounded(source,target,root,env,logs,seconds):
    logs.mkdir(parents=True,exist_ok=True)
    args=['lean',*ci.FLAGS,'-R',str(root)]
    if target is not None: args+=['-o',str(target)]
    args.append(str(source));start=time.monotonic();code=124
    with (logs/(source.stem+'.log')).open('w') as log:
        try:code=subprocess.run(args,cwd=ci.PROJECT,env=env,stdout=log,
                                stderr=subprocess.STDOUT,timeout=seconds).returncode
        except subprocess.TimeoutExpired:log.write('\nWALL_CLOCK_LIMIT_EXCEEDED\n')
    row={'module':source.stem,'exit_code':code,'seconds':round(time.monotonic()-start,3)}
    print(json.dumps(row),flush=True)
    return row


def run(args,plan):
    folder,data,direct,external=packet(args.packet,plan)
    output=args.output.resolve();output.mkdir(parents=True,exist_ok=False)
    lib=output/'lib';lib.mkdir();logs=output/'logs'
    result={'status':'PENDING','packet':args.packet,'packet_sha256':ci.sha(folder/'intake.json'),
            'baseline_snapshot':plan['snapshot'],'baseline_modules':len(plan['module_order']),
            'commands':[],'new_source_acceptance':False,'full_arithmetic_theorem_proved':False}
    try:
        needed=required_baseline(plan,direct)
        restore_baseline(args.cache.resolve(),lib,plan,needed)
        result['verified_predecessors_reused']=len(needed)
        env,version=ci.environment(ci.PROJECT,lib);result['toolchain']=version
        ci.ensure_official(ci.PROJECT,env,logs)
        # Direct additional upstream imports are fetched by the preceding pinned cache step.
        for dep in external:
            if dep.split('.')[0] in {'Lean','Std','Init'}:continue
            if not any((Path(p)/(dep.replace('.','/')+'.olean')).is_file()
                       for p in env['LEAN_PATH'].split(os.pathsep)):
                raise ValueError('Missing pinned upstream artifact: '+dep)
        for n in data['order']:
            row=compile_bounded(folder/(n+'.lean'),lib/(n+'.olean'),folder,env,logs,args.seconds)
            result['commands'].append(row);ci.write_json(output/'RESULT.json',result)
            if row['exit_code']:raise RuntimeError('Draft first check failed: '+n)
        audit=output/'ExperimentAudit.lean';audit.write_text(audit_text(data['order']))
        row=compile_bounded(audit,None,output,env,logs,args.seconds);result['commands'].append(row)
        if row['exit_code']:raise RuntimeError('Packet axiom audit failed')
        m=re.search(r'EXPERIMENT_AUDIT_PASS declarations=(\d+) modules=(\d+)',
                    (logs/'ExperimentAudit.log').read_text())
        if not m or int(m[2])!=len(data['order']):raise ValueError('Incomplete packet audit')
        result.update(status='PASS',source_modules=len(data['order']),audited_declarations=int(m[1]),
                      allowed_axioms=['propext','Classical.choice','Quot.sound'],
                      scope='Individual strict checks and packet recursive audit; not promoted to accepted snapshot')
    except Exception as e:
        result.update(status='FAILED',error=str(e));raise
    finally:ci.write_json(output/'RESULT.json',result)


def main():
    if not __debug__:raise RuntimeError('Do not run with Python -O')
    a=argparse.ArgumentParser(description=__doc__);a.add_argument('command',choices=['plan','targets','check'])
    a.add_argument('--packet');a.add_argument('--cache',type=Path);a.add_argument('--output',type=Path)
    a.add_argument('--github-output',type=Path);a.add_argument('--seconds',type=int,default=180,choices=range(30,601))
    args=a.parse_args()
    if args.command != 'targets': ci.check_sources(ci.PROJECT)
    plan=ci.derive_plan(early_depth=7)
    if args.command=='plan':
        names=json.loads((EXPERIMENTS/'packets.json').read_text())['active_packets']
        if len(names)!=len(set(names)) or len(names)>16:raise ValueError('Invalid experiment matrix')
        for n in names:packet(n,plan)
        d={'matrix':{'packet':names},'base':plan['base'],'snapshot':plan['snapshot']};print(json.dumps(d))
        if args.github_output:
            with args.github_output.open('a') as f:
                for k,v in d.items():f.write(k+'='+(json.dumps(v,separators=(',',':')) if isinstance(v,dict) else v)+'\n')
    elif args.command=='targets':
        _,_,_,external=packet(args.packet,plan)
        print('\n'.join(sorted(x for x in set(plan['upstream'])|external
                               if x.split('.')[0] not in {'Lean','Std','Init'})))
    else:
        if args.cache is None or args.output is None:a.error('check requires cache and output')
        run(args,plan)

if __name__=='__main__':main()
