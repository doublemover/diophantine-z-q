from pathlib import Path
import sys,json,hashlib,subprocess,re,shutil
B=Path('/workspace/scratch/41c6d5925c0e');P=B/'geometry-point-derivation-instance-revision';R=B/'pel-followup43603177874/repo';O=B/'review43603177874';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();a=json.loads((P/'APPLICATION.json').read_text());f=json.loads((P/'FUTURE-CLOSURE.json').read_text())
assert H(P/'APPLICATION.json')=='59b1efb99bce1ee46a16411e5ee38bdca218c0bd1af91e1937e5dfb7f4f24ae7';assert not f['active'] and f['pending_context_is_not_dependency']
for n,h in a['bindings'].items():assert H(P/n)==h,(n,h)
for n,h in a['sources'].items():assert H(P/'sources'/n)==h
prev=P/'PRE-TAIL-REVISION';orig=P/'PRE-INSTANCE-REVISION';pa=json.loads((prev/'APPLICATION.json').read_text());oa=json.loads((orig/'APPLICATION.json').read_text());assert H(prev/'APPLICATION.json')==a['tactic_tail_revision']['reviewed_prior_application_sha256'];assert H(orig/'APPLICATION.json')==a['prior_application_sha256']
for n,h in pa['bindings'].items():assert H(prev/n)==h
for n,h in oa['bindings'].items():assert H(orig/n)==h
for n in a['sources']:
 b=(P/'sources'/n).read_text();p=(prev/'sources'/n).read_text();z=(orig/'sources'/n).read_text()
 if n=='FirstOrderCotangentEvaluation318.lean':
  assert b.replace('simp only [map_one,TrivSqZeroExt.snd_one]','rw [map_one]\n        rfl')==p
  assert 'local instance' not in b and 'letI : Algebra A K := f.toRingHom.toAlgebra' in b and 'letI : Algebra A V := f.toRingHom.toAlgebra' in b
 elif n=='NormalizedCotangentEvaluation318.lean':
  assert b.replace('rw [FourRootFirstOrderPoint318.lift_polynomial,Polynomial.aeval_X] <;> rfl','rw [FourRootFirstOrderPoint318.lift_polynomial,Polynomial.aeval_X]\n  rfl')==p==z
 else:assert b==p==z
native=json.loads((P/'primary/NATIVE-PROVENANCE.json').read_text());project=json.loads((P/'PROJECT-PROVENANCE.json').read_text())
for row in native:
 p=P/'primary'/row['path'];b=p.read_bytes();assert H(p)==row['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['git_blob'];assert row['commit']=='56a005855ea17e0b0958f73ec801ae140b0a1679'
for row in project:
 p=P/row['path'];b=subprocess.check_output(['git','show',row['commit']+':'+row['repository_path']],cwd=R);assert p.read_bytes()==b;assert H(p)==row['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['git_blob']
sys.dont_write_bytecode=True;sys.path.insert(0,str(R/'scripts'));import check_progress_experiment as ce
plan=ce.ci.derive_plan();sources={};basepath='quartics/quartic-318-326/proof/experiments/'+f['base_packet'];head=f['base_commit'];pd=json.loads(subprocess.check_output(['git','show',head+':'+basepath+'/intake.json'],cwd=R));assert len(f['unchanged_predecessor_sources'])==96 and pd['order']==f['proposed_order'][:96]
for n,h in f['unchanged_predecessor_sources'].items():
 b=subprocess.check_output(['git','show',head+':'+basepath+'/'+n],cwd=R);assert hashlib.sha256(b).hexdigest()==h==pd['files'][n]['sha256'];sources[n[:-5]]=b.decode()
for n,h in a['sources'].items():sources[n[:-5]]=(P/'sources'/n).read_text()
assert len(sources)==len(f['proposed_order'])==100 and set(sources)==set(f['proposed_order']);seen=set();direct=set()
for n in f['proposed_order']:
 code=ce.code_only(sources[n]);assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|skipKernelTC)\b',code)
 for imp in ce.ci.import_names(sources[n]):
  if imp in seen:continue
  if imp in plan['module_keys']:direct.add(imp)
  else:assert imp.split('.')[0] in ce.OFFICIAL_PREFIXES,(n,imp,'missing/order')
 seen.add(n)
for n in a['sources']:assert not re.search(r'^\s*set_option\b',sources[n[:-5]],re.M)
assert len(a['obligations'])==9
for ob in a['obligations']:
 for k in ['required_input','constructed_input','justification','source_refs','evidence']:assert ob[k]
 for ref in ob['source_refs']+ob['evidence']:assert (P/ref).is_file()
nb=(P/'primary/Mathlib_Algebra_TrivSqZeroExt_Basic.lean').read_text();nk=(P/'primary/Mathlib_RingTheory_Kaehler_Basic.lean').read_text();nt=(P/'primary/Mathlib_LinearAlgebra_TensorProduct_Tower.lean').read_text();np=(P/'primary/Mathlib_Algebra_Polynomial_AlgebraMap.lean').read_text()
assert 'theorem snd_one' in nb and 'theorem snd_mul' in nb and 'def sndHom' in nb
assert 'theorem Derivation.liftKaehlerDifferential_comp_D' in nk
assert 'nonrec def lift (f : M →ₗ[A] N →ₗ[R] P) : M ⊗[R] N →ₗ[A] P' in nt
assert 'aeval (f x) p = f (aeval x p)' in np
snap=O/'point-derivation-source-snapshots';snap.mkdir(exist_ok=True)
for n in set(a['bindings'])|{'APPLICATION.json'}:
 dest=snap/n;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(P/n,dest)
d={'status':'PASS_CORRECTED_RESEARCH_SOURCE_AND_CURRENT_CONTRACT_ONLY','application_sha256':H(P/'APPLICATION.json'),'sources':a['sources'],'obligations':a['obligations'],'inactive_closure':{'count':100,'published_unchanged':96,'new_sources':4,'required_baseline_count':len(ce.required_baseline(plan,direct))},'native_primary_count':len(native),'project_primary_count':len(project),'preserved_original_application_sha256':H(orig/'APPLICATION.json'),'preserved_pre_tail_application_sha256':H(prev/'APPLICATION.json'),'hidden_f_instance_registrations_removed':True,'local_lean_run':False,'kernel_verified':False,'original_hn_adapter_reviewed':False,'global_model_or_KS_constructed':False,'source_bindings':{str(p.relative_to(B)):H(p) for p in snap.rglob('*') if p.is_file()}}
(O/'POINT-DERIVATION-SOURCE-CHECK.json').write_text(json.dumps(d,indent=2)+'\n');print('PASS: corrected4 source hashes, complete original/tail snapshots, native9/project11 identities, unchanged96+4 inactive100 closure, 9 obligations; source only.')
