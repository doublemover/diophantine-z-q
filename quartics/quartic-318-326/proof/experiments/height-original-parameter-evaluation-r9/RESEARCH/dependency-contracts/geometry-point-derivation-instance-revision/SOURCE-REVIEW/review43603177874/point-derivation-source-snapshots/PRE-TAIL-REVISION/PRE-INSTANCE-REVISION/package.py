from pathlib import Path
import hashlib,json,subprocess,shutil,re,tarfile
r=Path(__file__).resolve().parent;root=r.parent;repo=root/'pel-integration43597228569/repo';head='57227e167abe49436d651b932ff75d5bdf9b5898';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();pre='quartics/quartic-318-326/proof/experiments/height-normalized-valuative-center-r68/'
# All fetched native blobs are exact API content, checked against the pinned tree.
tree=json.loads((r/'primary/MATHLIB-TREE.json').read_text());assert not tree['truncated'];entries={x['path']:x['sha'] for x in tree['tree']};assert tree['sha']=='56a005855ea17e0b0958f73ec801ae140b0a1679'
native=[]
for p in sorted((r/'primary').glob('*.json')):
 if p.name=='MATHLIB-TREE.json':continue
 j=json.loads(p.read_text())
 if not isinstance(j,dict) or not {'content','sha','path'}<=j.keys():continue
 import base64
 b=base64.b64decode(j['content']);assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==j['sha']==entries[j['path']]
 n=j['path'].replace('/','_');dest=r/'primary'/n
 if not dest.exists():dest.write_bytes(b)
 assert dest.read_bytes()==b
 native.append({'path':n,'repository_path':j['path'],'commit':tree['sha'],'git_blob':j['sha'],'sha256':sha(dest),'api_response':p.name})
for row in json.loads((root/'geometry-module-image-frames/primary/NATIVE-PROVENANCE.json').read_text()):
 if row['repository_path'] in ['Mathlib/LinearAlgebra/TensorProduct/Tower.lean','Mathlib/RingTheory/Kaehler/Basic.lean']:
  p=root/'geometry-module-image-frames/primary'/row['path'];assert sha(p)==row['sha256'];shutil.copy2(p,r/'primary'/p.name);native.append(row)
(r/'primary/NATIVE-PROVENANCE.json').write_text(json.dumps(native,indent=2)+'\n')
project=[];paths=[pre+n+'.lean' for n in ['IntegralRootPointMaps318','DVRNormalizedFiniteOrder318','DVRNormalizedInfinityOrder318','DVRNormalizedAllPlaceCharts318']]+['quartics/quartic-318-326/proof/progress/'+n+'.lean' for n in ['FourRootOrder318','FourRootOrderSigns318']]+['quartics/quartic-318-326/proof/experiments/height-original-ks-lattice-assembly-r16/'+n+'.lean' for n in ['RationalContactPoint318','RationalFourRootFiber318','OriginalPointFinitePlaceRoots318','OriginalBranchCotangentFiber318','ContactBicanonicalPointHeight318']]
for path in paths:
 b=subprocess.check_output(['git','-C',str(repo),'show',head+':'+path]);p=r/'primary'/Path(path).name;p.write_bytes(b);project.append({'path':'primary/'+p.name,'repository_path':path,'commit':head,'git_blob':subprocess.check_output(['git','-C',str(repo),'rev-parse',head+':'+path]).decode().strip(),'sha256':sha(p)})
(r/'PROJECT-PROVENANCE.json').write_text(json.dumps(project,indent=2)+'\n')
for folder in ['geometry-module-image-frames','geometry-normalized-cotangent-inputs']:
 out=r/'pending-context'/folder;out.mkdir(parents=True,exist_ok=True)
 for p in sorted((root/folder).rglob('*')):
  if p.is_file() and not p.name.endswith('.tar.gz') and p.name!='ARCHIVE-RECEIPT.json':
   dest=out/p.relative_to(root/folder);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dest)
old=json.loads(subprocess.check_output(['git','-C',str(repo),'show',head+':'+pre+'intake.json']))
for n,row in old['files'].items():assert hashlib.sha256(subprocess.check_output(['git','-C',str(repo),'show',head+':'+pre+n])).hexdigest()==row['sha256']
new=['FourRootFirstOrderPoint318','NormalizedFirstOrderPoints318','FirstOrderCotangentEvaluation318','NormalizedCotangentEvaluation318'];order=old['order']+new;assert len(order)==len(set(order))==100
sources={p.name:sha(p) for p in sorted((r/'sources').glob('*.lean'))};assert len(sources)==4
seen=set(old['order'])
for n in new:
 s=(r/'sources'/(n+'.lean')).read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b|set_option',s)
 for dep in re.findall(r'^public import (\w[\w.]*)',s,re.M):assert dep in seen or dep.startswith('Mathlib.'),(n,dep)
 seen.add(n)
plan={'active':False,'base_commit':head,'base_packet':'height-normalized-valuative-center-r68','unchanged_predecessor_sources':{n:e['sha256'] for n,e in old['files'].items()},'new_sources':sources,'proposed_order':order,'pending_context_is_not_dependency':True};(r/'FUTURE-CLOSURE.json').write_text(json.dumps(plan,indent=2)+'\n')
ob=[
('required_inputs','Actual V-algebra integral chart point, its full polynomial evaluation at t, nonzero values of all four root generators, characteristic-zero K.','Root square identities derived from the same generator_square; concrete first-order root relations construct the lift.','No generic derivation/frame/functional premise; complete automatic original hn adapter is still pending.'),
('constructed_objects','Whole original finite/reciprocal four-root order and its actual integral cotangent pullback.','First-order point, its derivation, native universal differential map and balanced V-tensor evaluation are defined.','No quotient/dense-open source replacement or arbitrary lattice choice.'),
('index_and_domain_coverage','All four signed roots and entire polynomial coefficient algebra, both actual chart formulas.','Projection_eq checks full base and every Fin4 root; both normalized coefficient formulas are used.','Zero root points are excluded by explicit hn for this route, not silently covered; prior all-point chart producer unchanged.'),
('transition_maps','Projection from TrivSqZeroExt, native Kaehler universal map, actual A→V→K balanced tensor lift.','Projection equals the same original point globally; derivative evaluated on 1 tensor Da equals the first-order component.','No alternative A-action, new field or Omega(K/V) replacement.'),
('scalars_and_signs','Finite derivative d_i/(2z_i); reciprocal d_i*(1-2a_i*w)/(2z_i); prescribed signs of z_i.','These exact scalars are proved in K, with finite DT=1 and reciprocal Dw=1.','Dw is not identified with original Dt; required -t^-2 transition and rational-frame scale remain open.'),
('consumer_identity','Frozen pending finite-cotangent-image consumer requires ev plus original quadratic section lifts.','The constructed map has its exact V tensor_A Omega carrier and is linear over the original V.','Original section lifts/evaluations and maximal dualizing-image identity are NOT supplied here.'),
('exceptional_cases','Potential residue characteristic two, nonunit twists, singular/torsion integral cotangents, and zero roots.','Field characteristic zero permits 2 inverses only in K; no integral unit-2 premise. Kernel/torsion is allowed.','No regularity, source rank one or injectivity follows; zero roots require another route.'),
('downstream_and_history','Exact original signed points, integral model comparisons and eventual native KS/height inputs.','No existing source is mutated, only four new inactive sources and preserved primary context.','No native KS, dualizing/maximal model, metric, degree or historical new-gap claim.'),
('verification_boundary','Independent four-source/current-contract review before any reachable hosted experiment.','Pinned native/project provenance, exact100 future closure and static/audit checks.','No local Lean, admissions, compiler/resource/cache change or proof/packet acceptance.')]
a={'author':'geometry_repair_resume','status':'SOURCE_REVIEW_PENDING_NOT_ACTIVE','local_lean_run':False,'kernel_verified':False,'evaluation_candidate_constructed':True,'original_hn_adapter_complete':False,'original_quadratic_section_lifts_constructed':False,'maximal_model_or_KS_constructed':False,'sources':sources,'obligations':[{'id':i,'required_input':q,'constructed_input':c,'justification':j,'source_refs':['README.md',*['sources/'+n for n in sources]],'evidence':['PROJECT-PROVENANCE.json','primary/NATIVE-PROVENANCE.json','FUTURE-CLOSURE.json']} for i,q,c,j in ob]}
cp=subprocess.run(['python','-B',str(repo/'scripts/check_audit_history.py'),'--self-test'],capture_output=True,text=True);(r/'audit-self-test.log').write_text(cp.stdout+cp.stderr);assert cp.returncode==0
exclude={'APPLICATION.json','geometry-point-derivation-audit.tar.gz','ARCHIVE-RECEIPT.json'};a['bindings']={str(p.relative_to(r)):sha(p) for p in sorted(r.rglob('*')) if p.is_file() and str(p.relative_to(r)) not in exclude};(r/'APPLICATION.json').write_text(json.dumps(a,indent=2)+'\n')
o=r/'geometry-point-derivation-audit.tar.gz';ps=sorted(p for p in r.rglob('*') if p.is_file() and p.name not in [o.name,'ARCHIVE-RECEIPT.json'])
with tarfile.open(o,'w:gz') as t:
 for p in ps:t.add(p,arcname=str(p.relative_to(r)))
with tarfile.open(o,'r:gz') as t:
 for p in ps:assert t.extractfile(str(p.relative_to(r))).read()==p.read_bytes()
d={'sha256':sha(o),'bytes':o.stat().st_size,'files':len(ps),'application_sha256':sha(r/'APPLICATION.json'),'sources':sources,'status':a['status']};(r/'ARCHIVE-RECEIPT.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d,indent=2))
