from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,"/workspace/scratch/41c6d5925c0e/geometry-ks66-rational-fiber-integration/scripts")
from check_progress_lean import import_names
W=Path('/workspace/scratch/41c6d5925c0e');R=W/'resume-20261115-repo';base='60300ddf3d03d1b62d2dc89b8f0c0ead7fb24718';pre='quartics/quartic-318-326/proof/experiments/height-original-ks-lattice-assembly-r67';progress='quartics/quartic-318-326/proof/progress'
def git(*a):return subprocess.check_output(['git','-C',str(R),*a])
def sha(b):return hashlib.sha256(b).hexdigest()
prior=json.loads(git('show',base+':'+pre+'/intake.json'));sources={n:git('show',base+':'+pre+'/'+n+'.lean') for n in prior['order']}
folders={
'NormalizationChartFieldPoint318':'geometry-normalization-generic-point-20261117',
'OriginalIntegerRationalGenericPoint318':'geometry-original-rational-generic-point-20261117',
'OriginalIntegerRationalOverlapEquality318':'geometry-rational-actual-overlap-equality-20261117',
'PullbackIntersectionBaseChange318':'geometry-pullback-intersection-basechange-20261117',
'OriginalIntegerRationalIntersection318':'geometry-rational-intersection-identification-20261117',
'IntegerRationalTensorNaturality318':'geometry-rational-tensor-naturality-20261117'}
predecessor_hashes={n:sha(b) for n,b in sources.items()}
repair_dir='recovery-geometry89-six-roots-44089536769-v2'
repair=json.loads((W/repair_dir/'SOURCE-APPLICATION.json').read_text())
for n,d in repair['changed_sources'].items():
 assert sha(sources[n])==d['before']
 sources[n]=(W/repair_dir/'after'/(n+'.lean')).read_bytes()
 assert sha(sources[n])==d['after']
for n,d in folders.items():sources[n]=(W/d/'sources'/(n+'.lean')).read_bytes()
names=git('ls-tree','--name-only',base+':'+progress).decode().splitlines();baselines={n[:-5]:git('show',base+':'+progress+'/'+n) for n in names if n.endswith('.lean')}
seen=set();active=set();order=[];bo=[]
def visit(n):
 if n.startswith(('Mathlib','Lean','Init','Std')):return
 if n in seen:return
 assert n not in active,('cycle',n)
 active.add(n);b=sources.get(n,baselines.get(n));assert b is not None,('missing',n)
 imports=sorted(import_names(b.decode()))
 for i in imports:visit(i)
 active.remove(n);seen.add(n)
 (order if n in sources else bo).append(n)
targets=['OriginalIntegerRationalTwoCover318','OriginalIntegerRationalOverlapEquality318','OriginalIntegerRationalIntersection318','IntegerRationalTensorNaturality318']
for n in targets:visit(n)
new=[n for n in order if n in folders];assert set(new)==set(folders)
v={'base_commit':base,'predecessor_packet':pre,'targets':targets,'target_order':order,'baseline_order':bo,'target_count':len(order),'baseline_count':len(bo),'target_hashes':{n:sha(sources[n]) for n in order},'baseline_hashes':{n:sha(baselines[n]) for n in bo},'predecessor_order':prior['order'],'predecessor_source_hashes':predecessor_hashes,'new_modules':new,'changed_modules':list(repair['changed_sources']),'repair_directory':repair_dir,'repair_application_sha256':sha((W/repair_dir/'SOURCE-APPLICATION.json').read_bytes()),'source_folders':folders,'source_applications':{n:sha((W/d/'SOURCE-APPLICATION.json').read_bytes())for n,d in folders.items()},'status':'SOURCE_AND_REBASE_REVIEW_PENDING_NOT_LEAN','scope':'Six exact runtime-root repairs plus six reviewed canonical-point, literal actual overlap equality, full categorical rational intersection and tensor naturality bridges. No global glued isomorphism/bad-prime regularity inferred; actual final intersection projection composition remains separate.','pending_dependencies':'Geometry89 exact73 strict/audit1607 retained, six failures repaired and ten blocked remain strict replay obligations. All pending KS67 and six new sources require full checked closure; no module inferred accepted from source gates.'}
p=W/'geometry-ks68-overlap-repair-plan-20261117/BATCH-PLAN.json';p.write_text(json.dumps(v,indent=2)+'\n');print(len(order),len(bo),sha(p.read_bytes()))
