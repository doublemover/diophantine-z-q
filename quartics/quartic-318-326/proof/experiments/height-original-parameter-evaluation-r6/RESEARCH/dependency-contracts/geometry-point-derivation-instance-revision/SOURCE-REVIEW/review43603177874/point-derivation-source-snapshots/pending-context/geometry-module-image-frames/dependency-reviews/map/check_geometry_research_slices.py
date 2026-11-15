from pathlib import Path
import json,hashlib,subprocess,re,shutil
B=Path('/workspace/scratch/41c6d5925c0e');O=B/'review43592150561';R=B/'pel-integration43592150561/repo';H='2b151fc62f5872fd569489336d35f536d4cae0a4';X='quartics/quartic-318-326/proof/experiments/'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for label,root in [('GEOMETRY-MODEL-MAP','geometry-model-map-slice'),('GEOMETRY-SECTION-DEFECT','geometry-section-lattice-slice')]:
 W=B/root;A=json.loads((W/'APPLICATION.json').read_text());C=json.loads((W/'FUTURE-CLOSURE.json').read_text());P=json.loads((W/'PROVENANCE.json').read_text());P=P['files'] if isinstance(P,dict) else P
 S=O/'source-snapshots'/root;S.mkdir(parents=True,exist_ok=True)
 refs=set(['APPLICATION.json','FUTURE-CLOSURE.json','PROVENANCE.json'])
 for rel,h in A['bindings'].items():assert sha(W/rel)==h,(root,rel);refs.add(rel)
 assert len(A['obligations'])==9 and len({o['id'] for o in A['obligations']})==9
 for o in A['obligations']:
  for k in ['required_input','constructed_input','justification']:assert o[k]
  for k in ['source_references','evidence']:
   assert o[k]
   for rel in o[k]:assert (W/rel).is_file(),rel;refs.add(rel)
 assert not A['production_changes'] and not A['local_lean_run'] and not A['global_realization_proved'] and not C['active']
 for p in P:
  data=(W/p['path']).read_bytes();assert sha(W/p['path'])==p['sha256']
  actual=subprocess.check_output(['git','show',p['commit']+':'+p['repository_path']],cwd=R);assert data==actual
  if 'git_blob' in p:assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==p['git_blob']
  refs.add(p['path'])
 native=W/'primary/NATIVE-API-PROVENANCE.json'
 if native.exists():
  refs.add(str(native.relative_to(W)))
  for p in json.loads(native.read_text()):
   data=(W/p['path']).read_bytes();assert sha(W/p['path'])==p['sha256'] and p['commit']=='56a005855ea17e0b0958f73ec801ae140b0a1679'
   assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==p['git_blob'];refs.add(p['path'])
 assert len(C['unchanged_predecessor_files'])==173 and len(C['candidate_files'])==3 and len(C['proposed_order'])==len(set(C['proposed_order']))==176
 for filename,v in C['unchanged_predecessor_files'].items():
  data=subprocess.check_output(['git','show',H+':'+X+C['base_packet']+'/'+filename],cwd=R);assert hashlib.sha256(data).hexdigest()==v['sha256']
 for filename,h in C['candidate_files'].items():
  p=W/'sources'/filename;assert sha(p)==h;refs.add(str(p.relative_to(W)));t=re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S);t=re.sub(r'--[^\n]*','',t)
  assert not re.search(r'\b(sorry|axiom|admit|unsafe|implemented_by|native_decide)\b|set_option',t)
 for rel in sorted(refs):
  d=S/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(W/rel,d)
 j={'status':'PASS_SOURCE_AND_STANDALONE_NINE_OBLIGATIONS_ONLY','root':root,'application_sha256':sha(W/'APPLICATION.json'),'candidate_sources':C['candidate_files'],'published_primary_count':len(P),'independently_checked_predecessor_sources':173,'inactive_closure':176,'local_lean_run':False,'candidate_hosted_pass':False,'global_realization_proved':False,'source_bindings':{str(p.relative_to(O)):sha(p) for p in S.rglob('*') if p.is_file()}}
 (O/(label+'-SOURCE-CHECK.json')).write_text(json.dumps(j,indent=2)+'\n');print(label,'PASS',len(refs),'bound files;',len(P),'published primary sources;173 predecessor hashes;3 candidates;9 obligations')
