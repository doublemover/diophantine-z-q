import sys,json,pathlib,subprocess,shutil,hashlib
r=pathlib.Path('/workspace/scratch/2cb21e4e0864/quartic-proof');sys.path.insert(0,str(r/'scripts'))
from check_progress_lean import import_names
from check_progress_experiment import packet,required_baseline,audit_text
p=r/'quartics/quartic-318-326/proof/experiments/affine-sheaf-basechange';e=p.parent
new=['TildePushforward318','AffineSheafBaseChange318','AffineOverlapCoaction318','OriginalLineOverlapCoaction318','AffineOverlapDiagonal318']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
base='5e483a2b186a83500f4b603f3ddfc514ae84a393';prefix='quartics/quartic-318-326/proof/progress/'
m=json.loads(subprocess.check_output(['git','show',f'{base}:{prefix}checkpoint-manifest.json'],cwd=r,text=True));bo=m['module_order'];bos=set(bo);deps={}
for n in bo:
 s=r/prefix/(n+'.lean');assert sha(s)==m['modules'][n]['sha256'];deps[n]=sorted(import_names(s.read_text())&bos)
plan={'module_keys':{n:None for n in bo},'dependencies':deps,'module_order':bo}
producer={}
for d in ['line-affine-basechange','affine-pushout-comparison']:
 for s in (e/d).glob('*.lean'):
  if s.stem in producer:assert sha(producer[s.stem])==sha(s)
  producer[s.stem]=s
order=[];seen=set()
def visit(n):
 if n in bos or n.split('.')[0]=='Mathlib':return
 if n in seen:return
 seen.add(n);s=p/(n+'.lean') if n in new else producer[n]
 for dep in sorted(import_names(s.read_text())):visit(dep)
 if n not in new:shutil.copy2(s,p/(n+'.lean'))
 order.append(n)
for n in new:visit(n)
i={'packet':p.name,'status':'PENDING_FRESH_CLOSURE_CHECK','order':order,'files':{n+'.lean':{'sha256':sha(p/(n+'.lean')),'imports':sorted(import_names((p/(n+'.lean')).read_text()))} for n in order},'new_modules':new,'unchanged_producer_modules':[n for n in order if n not in new],'scope':'Actual affine scheme pull-push comparison and bijective transport of original line overlap morphisms to candidate comonad maps. The actual normalized diagonal evaluation implies the counit law. Triple-overlap coassociativity, scheme-mate identification and effective geometric fppf descent are not asserted.','new_source_acceptance':False,'full_arithmetic_theorem_proved':False}
(p/'intake.json').write_text(json.dumps(i,indent=2)+'\n');_,_,direct,external=packet(p.name,plan);needed=required_baseline(plan,direct)
d={'baseline_commit':base,'baseline_snapshot':'768c64ba67b1e1901c7492948ef3b1e727f49e38641664e00d435d45d8bc96a8','direct_baseline':sorted(direct),'baseline_closure':needed,'upstream':sorted(external),'unchanged_producers':{n:{'source':str(producer[n].relative_to(r)),'sha256':sha(producer[n])} for n in order if n not in new}}
(p/'DEPENDENCIES.json').write_text(json.dumps(d,indent=2)+'\n');(p/'MODULE_ORDER.txt').write_text('\n'.join(order)+'\n');(p/'SOURCE_SHA256SUMS').write_text(''.join(sha(p/(n+'.lean'))+'  '+n+'.lean\n' for n in order))
b=pathlib.Path('/workspace/shared/affine-sheaf-basechange-final');(b/'lib').mkdir(parents=True,exist_ok=True);(b/'logs').mkdir(exist_ok=True);(b/'ExperimentAudit.lean').write_text(audit_text(order))
print('Policy/source/closed-import checks PASS:',len(order),'sources,',len(new),'new,',len(needed),'baseline predecessors.')
