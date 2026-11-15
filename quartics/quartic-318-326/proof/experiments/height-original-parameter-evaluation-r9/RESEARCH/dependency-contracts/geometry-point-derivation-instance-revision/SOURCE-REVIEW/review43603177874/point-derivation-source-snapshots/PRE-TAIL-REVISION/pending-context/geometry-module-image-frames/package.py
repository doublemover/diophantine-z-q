from pathlib import Path
import json,hashlib,subprocess,shutil,tarfile,re
r=Path(__file__).resolve().parent;root=r.parent;repo=root/'pel-integration43597228569/repo';head='57227e167abe49436d651b932ff75d5bdf9b5898';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();pre='quartics/quartic-318-326/proof/experiments/height-original-ks-lattice-assembly-r16/'
(r/'dependencies').mkdir(exist_ok=True)
for folder in ['geometry-model-map-slice','geometry-fg-model-frames']:
 for p in (root/folder/'sources').glob('*.lean'):shutil.copy2(p,r/'dependencies'/p.name)
# Exact native previous finiteness APIs; copy the original provenance rows.
native=json.loads((r/'primary/NATIVE-PROVENANCE.json').read_text())
for row in json.loads((root/'geometry-fg-model-frames/primary/PROVENANCE.json').read_text()):
 p=root/'geometry-fg-model-frames/primary'/row['path'];assert sha(p)==row['sha256'];shutil.copy2(p,r/'primary'/p.name);native.append(row)
(r/'primary/NATIVE-PROVENANCE.json').write_text(json.dumps(native,indent=2)+'\n')
project=[]
for name in ['ActualFinitePlaceIntegers318','FinitePlacePrincipalLattice318','FinitePlacePrincipalImage318','OriginalCanonicalFiniteLattices318','OriginalExcludedPlaceData318','OriginalFiniteNormAssembly318','ContactBicanonicalPointHeight318']:
 path=pre+name+'.lean';b=subprocess.check_output(['git','-C',str(repo),'show',head+':'+path]);p=r/'primary'/(name+'.lean');p.write_bytes(b);project.append({'path':'primary/'+p.name,'repository_path':path,'commit':head,'git_blob':subprocess.check_output(['git','-C',str(repo),'rev-parse',head+':'+path]).decode().strip(),'sha256':sha(p)})
for tag,mpname in [('frame','GEOMETRY-FG-SOURCE-BINDINGS.json'),('map','GEOMETRY-MODEL-MAP-SOURCE-BINDINGS.json')]:
 mp=root/'review43592150561'/mpname;m=json.loads(mp.read_text());fs=dict(m['source_bindings']);fs[mp.name]=sha(mp)
 for n,h in fs.items():
  p=mp.parent/n;assert sha(p)==h;nout=r/'dependency-reviews'/tag/n;nout.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,nout)
(r/'PROJECT-PROVENANCE.json').write_text(json.dumps(project,indent=2)+'\n')
old=json.loads(subprocess.check_output(['git','-C',str(repo),'show',head+':'+pre+'intake.json']))
for n,row in old['files'].items():assert hashlib.sha256(subprocess.check_output(['git','-C',str(repo),'show',head+':'+pre+n])).hexdigest()==row['sha256']
depo=['EmbeddedLatticeFrames318','OriginalExcludedModelFrames318','OriginalModelMapMetricSections318','FiniteGeneratedPlaceFrame318','OriginalFiniteModelFrames318'];neworder=['FiniteModuleImageFrame318','OriginalFiniteImageModels318','FiniteCotangentImage318','OriginalFiniteCotangentModels318'];order=old['order']+depo+neworder;assert len(order)==len(set(order))==182
sources={p.name:sha(p) for p in sorted((r/'sources').glob('*.lean'))};deps={p.name:sha(p) for p in sorted((r/'dependencies').glob('*.lean'))};assert len(deps)==5
for p in (r/'sources').glob('*.lean'):assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b|set_option',p.read_text())
plan={'active':False,'base_commit':head,'base_packet':'height-original-ks-lattice-assembly-r16','unchanged_predecessor_sources':{n:e['sha256'] for n,e in old['files'].items()},'reviewed_dependency_sources':deps,'new_sources':sources,'proposed_order':order,'scope':'Inactive source-only finite image and cotangent pullback construction, no global model/KS claim.'};(r/'FUTURE-CLOSURE.json').write_text(json.dumps(plan,indent=2)+'\n')
ob=[
('required_inputs','Finite integral module and actual evaluation; cotangent specialization essential finite type A/V, point A→V, functional and original lifts.','Image FG is derived from native finiteness, not assumed; frame derives from original nonzero a0.','Actual chart/functional/model existence is still supplied.'),
('constructed_objects','Genuine evaluation image in original K.','Range, finite generation, generator, free frame and quadratic evaluation are constructed.','No arbitrary rank-one replacement or caller image-FG premise.'),
('index_and_domain_coverage','Every excluded place and both original sections, same K and Integers w.','Dependent all-bad-place family feeds existing full good/bad assembly.','Good-place lattices unchanged; no missing-index truncation.'),
('transition_maps','Pullback V tensor_A Omega(A/V), then V tensor-square, then literal bilinear evaluation.','On pure tensors the image is product of the SAME supplied cotangent functional.','Not Omega(K/V), no dualizing identification inferred.'),
('scalars_and_signs','Actual normalized finite-place valuation ring and original linear scalar structures.','Native base-change finiteness, finite image and norm-max generator use these rings.','No metric/degree/KS or defect-sign conclusion claimed.'),
('consumer_identity','OriginalFiniteModelFrames and OriginalExcludedModelFrames; original a0/a1.','All bad assembled lattices equal exact evaluated ranges; original lift equations provide membership.','Still must identify these ranges with actual regular/maximal bicanonical model.'),
('exceptional_cases','Nonzero evaluated a0; possible torsion/kernel/singular charts.','No injectivity or rank of source module required; zero image excluded by a0.','Normality alone supplies neither finite type nor regularity/dualizing square.'),
('downstream_and_history','Prior reviewed model/frame producer and actual original lattice consumer.','Exact five dependency sources and all companion reviews retained.','Global models, Hodge/KS, complex and bad-model comparisons remain unconstructed; no new-gap historical claim.'),
('verification_boundary','Independent four-source/current contract review and future hosted kernel checking.','Static no-admission/provenance/182-closure checks only.','No local Lean, active index, resource changes, acceptance or GeometricRealization.')]
a={'author':'geometry_repair_resume','status':'SOURCE_REVIEW_PENDING_NOT_ACTIVE','local_lean_run':False,'kernel_verified':False,'global_model_or_KS_constructed':False,'sources':sources,'dependencies':deps,'obligations':[{'id':i,'required_input':q,'constructed_input':c,'justification':j,'source_refs':['README.md',*['sources/'+n for n in sources]],'evidence':['PROJECT-PROVENANCE.json','primary/NATIVE-PROVENANCE.json','FUTURE-CLOSURE.json']} for i,q,c,j in ob]}
a['bindings']={str(p.relative_to(r)):sha(p) for p in sorted(r.rglob('*')) if p.is_file() and str(p.relative_to(r)) not in ['APPLICATION.json','geometry-module-image-frames.tar.gz','ARCHIVE-RECEIPT.json']};(r/'APPLICATION.json').write_text(json.dumps(a,indent=2)+'\n')
o=r/'geometry-module-image-frames.tar.gz';ps=sorted(p for p in r.rglob('*') if p.is_file() and p.name not in [o.name,'ARCHIVE-RECEIPT.json'])
with tarfile.open(o,'w:gz') as t:
 for p in ps:t.add(p,arcname=str(p.relative_to(r)))
with tarfile.open(o,'r:gz') as t:
 for p in ps:assert t.extractfile(str(p.relative_to(r))).read()==p.read_bytes()
d={'sha256':sha(o),'bytes':o.stat().st_size,'files':len(ps),'application_sha256':sha(r/'APPLICATION.json'),'sources':sources,'status':a['status']};(r/'ARCHIVE-RECEIPT.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d,indent=2))
