from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,"/workspace/scratch/41c6d5925c0e/geometry-ks66-rational-fiber-integration/scripts")
from check_progress_lean import import_names
W=Path('/workspace/scratch/41c6d5925c0e');R=W/'resume-20261115-repo';base='2954b51537ad8cba6aeb5870cfa8cc66adee18d8';pre='quartics/quartic-318-326/proof/experiments/height-original-ks-lattice-assembly-r66';progress='quartics/quartic-318-326/proof/progress'
def git(*a):return subprocess.check_output(['git','-C',str(R),*a])
def sha(b):return hashlib.sha256(b).hexdigest()
prior=json.loads(git('show',base+':'+pre+'/intake.json'));sources={n:git('show',base+':'+pre+'/'+n+'.lean') for n in prior['order']}
folders={
'OriginalIntegerReciprocalRationalParameter318':'geometry-reciprocal-rational-parameter-20261117',
'OriginalIntegerRationalReciprocalChart318':'geometry-rational-reciprocal-chart-identification-20261117',
'IntegerTensorFieldSquares318':'geometry-rational-tensor-field-squares-20261117',
'OriginalIntegerRationalOverlapSquares318':'geometry-rational-tensor-field-squares-20261117',
'OriginalIntegerRationalChartFieldSquares318':'geometry-rational-chart-field-squares-20261117',
'OriginalIntegerRationalTwoCover318':'geometry-rational-two-cover-comparison-20261117'}
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
targets=['OriginalIntegerRationalTwoCover318','OriginalIntegerRationalChartFieldSquares318']
for n in targets:visit(n)
new=[n for n in order if n in folders];assert set(new)==set(folders)
v={'base_commit':base,'predecessor_packet':pre,'targets':targets,'target_order':order,'baseline_order':bo,'target_count':len(order),'baseline_count':len(bo),'target_hashes':{n:sha(sources[n]) for n in order},'baseline_hashes':{n:sha(baselines[n]) for n in bo},'predecessor_order':prior['order'],'predecessor_source_hashes':{n:sha(sources[n])for n in prior['order']},'new_modules':new,'changed_modules':[],'source_folders':folders,'source_applications':{n:sha((W/d/'SOURCE-APPLICATION.json').read_bytes())for n,d in folders.items()},'status':'SOURCE_AND_REBASE_REVIEW_PENDING_NOT_LEAN','scope':'Exact whole reciprocal rational chart identification, actual original-model two-chart cover and objectwise comparison, canonical integer-only rational overlap embeddings and both original-chart field squares. No section-restriction compatibility/global scheme isomorphism or bad-prime regularity claimed.','pending_dependencies':'Full KS65/KS66 chain and all six additions require strict replay/audit; CommonField57 and reciprocal48 accepted independently.'}
p=W/'geometry-ks67-original-rational-chart-plan-20261117/BATCH-PLAN.json';p.write_text(json.dumps(v,indent=2)+'\n');print(len(order),len(bo),sha(p.read_bytes()))
