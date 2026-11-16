from pathlib import Path
import json,hashlib,subprocess,shutil,re,tarfile
r=Path(__file__).resolve().parent;root=r.parent;repo=root/'pel-integration43597228569/repo';head='57227e167abe49436d651b932ff75d5bdf9b5898';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pre='quartics/quartic-318-326/proof/experiments/height-normalized-valuative-center-r68/'
# Preserve the exact native finiteness lemmas and their original Git-blob identities.
native=json.loads((r/'primary/NATIVE-PROVENANCE.json').read_text())
for row in json.loads((root/'geometry-module-image-frames/primary/NATIVE-PROVENANCE.json').read_text()):
 if row['repository_path'] in ['Mathlib/RingTheory/Kaehler/Basic.lean','Mathlib/RingTheory/TensorProduct/Finite.lean']:
  p=root/'geometry-module-image-frames/primary'/row['path'];assert sha(p)==row['sha256'];shutil.copy2(p,r/'primary'/p.name)
  if row not in native:native.append(row)
for row in native:
 p=r/'primary'/row['path'];assert sha(p)==row['sha256'];b=p.read_bytes();assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['git_blob']
(r/'primary/NATIVE-PROVENANCE.json').write_text(json.dumps(native,indent=2)+'\n')
project=[]
names=['DVRNormalizedFiniteOrder318','DVRNormalizedInfinityOrder318','DVRNormalizedAllPlaceCharts318','NormalizedValuativeChartStructure318','NormalizedOriginalValuativeCenter318']
paths=[pre+n+'.lean' for n in names]+['quartics/quartic-318-326/proof/progress/FourRootOrderSigns318.lean','quartics/quartic-318-326/proof/progress/FourRootOrder318.lean','quartics/quartic-318-326/proof/experiments/height-original-ks-lattice-assembly-r16/FramedCotangentFiber318.lean']
for path in paths:
 b=subprocess.check_output(['git','-C',str(repo),'show',head+':'+path]);p=r/'primary'/Path(path).name;p.write_bytes(b);project.append({'path':'primary/'+p.name,'repository_path':path,'commit':head,'git_blob':subprocess.check_output(['git','-C',str(repo),'rev-parse',head+':'+path]).decode().strip(),'sha256':sha(p)})
(r/'PROJECT-PROVENANCE.json').write_text(json.dumps(project,indent=2)+'\n')
c=root/'geometry-module-image-frames';out=r/'consumer-pending-review';out.mkdir(exist_ok=True)
for p in [c/'APPLICATION.json',c/'README.md',*sorted((c/'sources').glob('*.lean'))]:shutil.copy2(p,out/p.name)
old=json.loads(subprocess.check_output(['git','-C',str(repo),'show',head+':'+pre+'intake.json']))
for n,row in old['files'].items():assert hashlib.sha256(subprocess.check_output(['git','-C',str(repo),'show',head+':'+pre+n])).hexdigest()==row['sha256']
order=old['order']+['NormalizedChartFiniteType318','NormalizedIntegralPointInput318'];assert len(order)==len(set(order))==98
sources={p.name:sha(p) for p in sorted((r/'sources').glob('*.lean'))};assert len(sources)==2
sysdeps=set(old['order']);base=json.loads(subprocess.check_output(['git','-C',str(repo),'show',head+':quartics/quartic-318-326/proof/progress/checkpoint-manifest.json']))
# Check every new direct import is native or earlier in the proposed unchanged closure.
for name in order[-2:]:
 p=r/'sources'/(name+'.lean');s=p.read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b|set_option',s)
 for dep in re.findall(r'^public import (\w[\w.]*)',s,re.M):assert dep in sysdeps or dep.startswith('Mathlib.'),(name,dep)
 sysdeps.add(name)
plan={'active':False,'base_commit':head,'base_packet':'height-normalized-valuative-center-r68','unchanged_predecessor_sources':{n:e['sha256'] for n,e in old['files'].items()},'new_sources':sources,'proposed_order':order,'pending_consumer_is_not_dependency':True}
(r/'FUTURE-CLOSURE.json').write_text(json.dumps(plan,indent=2)+'\n')
ob=[
('required_inputs','Native finite-type transitivity, module-finite four-root orders; DVR uniformizer and original full signed field-point equations.','Finite type derived for each named order. Existing chart_center supplies the ring point, scalar_identity supplies its base-linearity.','No model/point/finite-type premise is added for those concrete chart orders.'),
('constructed_objects','Actual normalized finite/reciprocal orders and integral point, then true cotangent pullback and square.','The same order, ring map and point-induced algebra structure are used; finite cotangent modules are constructed.','A V-linear functional and original section lifts are not constructed or hidden.'),
('index_and_domain_coverage','All four original signed roots, both finite and reciprocal cases, every DVR satisfying original inputs.','All u/e/s witnesses and original polynomial/root identities are carried through unchanged.','Includes nonunit twists, characteristic two and nonintegral t; no good-prime restriction.'),
('transition_maps','Underlying ring point, induced A-action on V, compatible V→A→V, then V tensor_A Omega(A/V).','pointAlgHom_toRingHom is rfl; scalar_identity fixes base constants and of_algHom proves tower compatibility.','No localization, coordinate/root substitution, alternate algebra action or dualizing identification.'),
('scalars_and_signs','Original twist factorization c_i=d_i*s_i² and roots y_i, reciprocal relation s_i*t*f(root_i)=y_i.','The original s, e, finite T, reciprocal w and all sign-sensitive equations remain literal.','No root choice/square root of global KS scalar, metric or degree sign is asserted.'),
('consumer_identity','Pending finite cotangent image consumer expects a compatible integral point on finite-type A and a functional with section lifts.','This supplies the named A, point and finiteness, without replacing that consumer range or original sections.','Exact pending consumer source/context is retained; full composition/model identification still open.'),
('exceptional_cases','t=0 finite case, reciprocal t≠0 and nonunit w; possible singular/torsion cotangents at bad places.','The existing disjunction and exceptional conditions are preserved. No regularity/rank/injectivity is deduced from finite generation.','Normalized twist orders need not be normal, regular or maximal; good-chart free cotangent frames cannot be silently reused.'),
('downstream_and_history','Full original point/whole model and eventual cotangent-image/maximal-dualizing/KS consumers.','Only actual chart prerequisites are advanced; inherited sources and earlier conditional bridges are unchanged.','Historical global applicability remains unresolved; no claim of a new gap or completed native KS construction.'),
('verification_boundary','Independent source/current contract review then reachable hosted kernel experiment.','Static provenance/import/no-admission/98-source future-closure and audit checks only.','No active index, local Lean, compiler/resource/cache changes or GeometricRealization claim.')]
a={'author':'geometry_repair_resume','status':'SOURCE_REVIEW_PENDING_NOT_ACTIVE','local_lean_run':False,'kernel_verified':False,'regular_or_maximal_model_constructed':False,'evaluation_functional_constructed':False,'global_KS_constructed':False,'sources':sources,'obligations':[{'id':i,'required_input':q,'constructed_input':c,'justification':j,'source_refs':['README.md',*['sources/'+n for n in sources]],'evidence':['PROJECT-PROVENANCE.json','primary/NATIVE-PROVENANCE.json','FUTURE-CLOSURE.json','consumer-pending-review/APPLICATION.json']} for i,q,c,j in ob]}
cp=subprocess.run(['python','-B',str(repo/'scripts/check_audit_history.py'),'--self-test'],capture_output=True,text=True);(r/'audit-self-test.log').write_text(cp.stdout+cp.stderr);assert cp.returncode==0
exclude={'APPLICATION.json','geometry-normalized-cotangent-inputs.tar.gz','ARCHIVE-RECEIPT.json'};a['bindings']={str(p.relative_to(r)):sha(p) for p in sorted(r.rglob('*')) if p.is_file() and str(p.relative_to(r)) not in exclude};(r/'APPLICATION.json').write_text(json.dumps(a,indent=2)+'\n')
o=r/'geometry-normalized-cotangent-inputs.tar.gz';ps=sorted(p for p in r.rglob('*') if p.is_file() and p.name not in [o.name,'ARCHIVE-RECEIPT.json'])
with tarfile.open(o,'w:gz') as t:
 for p in ps:t.add(p,arcname=str(p.relative_to(r)))
with tarfile.open(o,'r:gz') as t:
 for p in ps:assert t.extractfile(str(p.relative_to(r))).read()==p.read_bytes()
d={'sha256':sha(o),'bytes':o.stat().st_size,'files':len(ps),'application_sha256':sha(r/'APPLICATION.json'),'sources':sources,'status':a['status']};(r/'ARCHIVE-RECEIPT.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d,indent=2))
