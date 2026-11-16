from pathlib import Path
import sys,json,hashlib,subprocess,re,shutil
B=Path('/workspace/scratch/41c6d5925c0e');P=B/'geometry-normalized-cotangent-inputs';R=B/'pel-followup43603177874/repo';O=B/'review43603177874';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();a=json.loads((P/'APPLICATION.json').read_text());f=json.loads((P/'FUTURE-CLOSURE.json').read_text())
assert sha(P/'APPLICATION.json')=='7c2949026c53cae218b92c1f9d5b6689e1cb5e3636068a96f882cd89b1e018e8';assert f['active'] is False and f['pending_consumer_is_not_dependency'] is True
for fn,h in a['sources'].items():assert sha(P/'sources'/fn)==h
for fn,h in a['bindings'].items():assert sha(P/fn)==h,(fn,'binding')
native=json.loads((P/'primary/NATIVE-PROVENANCE.json').read_text());project=json.loads((P/'PROJECT-PROVENANCE.json').read_text())
for row in native:
 p=P/'primary'/row['path'];b=p.read_bytes();assert sha(p)==row['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['git_blob'];assert row['commit']=='56a005855ea17e0b0958f73ec801ae140b0a1679'
for row in project:
 p=P/row['path'];b=subprocess.check_output(['git','show',row['commit']+':'+row['repository_path']],cwd=R);assert p.read_bytes()==b;assert sha(p)==row['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['git_blob']
sys.dont_write_bytecode=True;sys.path.insert(0,str(R/'scripts'));import check_progress_experiment as ce
plan=ce.ci.derive_plan();sources={};basepath='quartics/quartic-318-326/proof/experiments/'+f['base_packet'];H=f['base_commit'];pd=json.loads(subprocess.check_output(['git','show',H+':'+basepath+'/intake.json'],cwd=R));assert len(f['unchanged_predecessor_sources'])==96 and pd['order']==f['proposed_order'][:96]
for fn,h in f['unchanged_predecessor_sources'].items():
 b=subprocess.check_output(['git','show',H+':'+basepath+'/'+fn],cwd=R);assert hashlib.sha256(b).hexdigest()==h==pd['files'][fn]['sha256'];sources[fn[:-5]]=b.decode()
for fn,h in a['sources'].items():sources[fn[:-5]]=(P/'sources'/fn).read_text()
assert len(sources)==len(f['proposed_order'])==98 and set(sources)==set(f['proposed_order']);seen=set();direct=set()
for n in f['proposed_order']:
 code=ce.code_only(sources[n]);assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|skipKernelTC)\b',code)
 for imp in ce.ci.import_names(sources[n]):
  if imp in seen:continue
  if imp in plan['module_keys']:direct.add(imp)
  else:assert imp.split('.')[0] in ce.OFFICIAL_PREFIXES,(n,imp,'missing/order')
 seen.add(n)
for n in a['sources']:assert not re.search(r'^\s*set_option\b',sources[n[:-5]],re.M)
assert len(a['obligations'])==9 and len({o['id'] for o in a['obligations']})==9
for ob in a['obligations']:
 for k in ['required_input','constructed_input','justification','source_refs','evidence']:assert ob[k]
 for ref in ob['source_refs']+ob['evidence']:assert (P/ref).is_file()
# Literal all-place theorem result preserved except ring-hom to V-algebra-hom bundle.
old=(P/'primary/DVRNormalizedAllPlaceCharts318.lean').read_text().split('theorem chart_center ',1)[1].split(' := by',1)[0]
new=sources['NormalizedIntegralPointInput318'].split('theorem chart_center_alg ',1)[1].split(' := by',1)[0]
assert new.replace('→ₐ[V] V','→+* V')==old
# Exact pending consumer source copies match the separately authored image-source review.
img=json.loads((O/'GEOMETRY-IMAGE-SOURCE-BINDINGS.json').read_text())
for fn,h in img['sources'].items():assert sha(P/'consumer-pending-review'/fn)==h
nt=(P/'primary/Mathlib_RingTheory_TensorProduct_Finite.lean').read_text();nk=(P/'primary/Mathlib_RingTheory_Kaehler_Basic.lean').read_text();nf=(P/'primary/Mathlib_RingTheory_FiniteType.lean').read_text();na=(P/'primary/Mathlib_Algebra_Algebra_Tower.lean').read_text()
assert 'instance KaehlerDifferential.finite [EssFiniteType R S]' in nk
assert 'instance Module.Finite.base_change' in nt and 'Module.Finite A (TensorProduct R A M)' in nt and 'instance Module.Finite.tensorProduct' in nt
assert 'theorem trans [Algebra S A] [IsScalarTower R S A]' in nf and '[hRA : Module.Finite R A] : Algebra.FiniteType R A' in nf
assert 'instance (priority := 999) of_algHom' in na and '@IsScalarTower R A B _ f.toRingHom.toAlgebra.toSMul _' in na
snap=O/'normalized-cotangent-source-snapshots';snap.mkdir(exist_ok=True)
for fn in set(a['bindings'])|{'APPLICATION.json'}:
 dest=snap/fn;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(P/fn,dest)
d={'status':'PASS_RESEARCH_SOURCE_AND_CURRENT_CONTRACT_ONLY','application_sha256':sha(P/'APPLICATION.json'),'sources':a['sources'],'obligations':a['obligations'],'all_place_result_exact_except_ring_to_algebra_bundle':True,'inactive_closure':{'count':98,'published_unchanged':96,'new_sources':2,'required_baseline_count':len(ce.required_baseline(plan,direct))},'native_primary_count':len(native),'project_primary_count':len(project),'local_lean_run':False,'kernel_verified':False,'global_model_or_KS_constructed':False,'source_bindings':{str(p.relative_to(B)):sha(p) for p in snap.rglob('*') if p.is_file()}}
(O/'NORMALIZED-COTANGENT-SOURCE-CHECK.json').write_text(json.dumps(d,indent=2)+'\n');print('PASS: 2 sources, exact all-place result except ring-to-algebra bundle, 96 Git-pinned roots, inactive98 closure, 9 obligations, native5/project8 identities, pending consumer identities; source only.')
