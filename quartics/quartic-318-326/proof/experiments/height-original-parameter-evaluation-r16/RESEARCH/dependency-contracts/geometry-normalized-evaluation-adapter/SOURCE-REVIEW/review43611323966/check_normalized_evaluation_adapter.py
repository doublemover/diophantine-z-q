from pathlib import Path
import hashlib,json,subprocess,base64,re,shutil
B=Path('/workspace/scratch/41c6d5925c0e');W=B/'geometry-normalized-evaluation-adapter';O=B/'review43611323966';S=O/'normalized-evaluation-adapter-snapshots';S.mkdir(exist_ok=True);R=B/'pel-integration43603177874/repo';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();digest=lambda b:hashlib.sha256(b).hexdigest()
assert sha(W/'APPLICATION.json')=='609c20fdb43281bafedd2e0d4d61bd7d8bf803089bd9644e6159fb3bf9c54f6d';j=json.loads((W/'APPLICATION.json').read_text());c=json.loads((W/'FUTURE-CLOSURE.json').read_text());records={}
for n,h in j['bindings'].items():
 p=W/n;assert p.is_file() and p.resolve().is_relative_to(W.resolve()) and sha(p)==h,(n,h);records[n]=h
assert len(j['obligations'])==9 and len({x['id'] for x in j['obligations']})==9
for ob in j['obligations']:
 for k in ['required_input','constructed_input','justification']:assert ob[k]
 for k in ['source_refs','evidence']:
  assert ob[k]
  for n in ob[k]:assert (W/n).is_file(),(ob['id'],n)
selected=['APPLICATION.json','README.md','FUTURE-CLOSURE.json','package.py','audit-self-test.log','PRE-REVIEWED-DEPENDENCY/APPLICATION.json','PRE-REVIEWED-DEPENDENCY/README.md','PRE-REVIEWED-DEPENDENCY/FUTURE-CLOSURE.json'];sources={}
for n,h in j['sources'].items():
 p=W/'sources'/n;assert sha(p)==h;assert p.read_bytes()==(W/'PRE-REVIEWED-DEPENDENCY/sources'/n).read_bytes();sources[p.stem]=p.read_bytes();selected.append('sources/'+n)
assert sha(W/'PRE-REVIEWED-DEPENDENCY/APPLICATION.json')==j['dependency_update']['prior_application_sha256']
for dep,d in j['dependencies'].items():
 root=W/'dependency-snapshots'/dep;assert sha(root/'APPLICATION.json')==d['application_sha256'];dj=json.loads((root/'APPLICATION.json').read_text());selected.append(str((root/'APPLICATION.json').relative_to(W)))
 for n,h in d['sources'].items():
  p=root/'sources'/n;assert sha(p)==h;assert p.read_bytes()==(B/dep/'sources'/n).read_bytes();sources[p.stem]=p.read_bytes();selected.append(str(p.relative_to(W)))
 for key in ['review_report_sha256','review_bindings_sha256']:
  if key in d:
   matches=[p for p in (root/'SOURCE-REVIEW').rglob('*') if p.is_file() and sha(p)==d[key]];assert matches,(dep,key);selected.append(str(matches[0].relative_to(W)))
 # Recursively named owner binding files must retain their exact local bytes.
 for n,h in dj.get('bindings',{}).items():
  if isinstance(h,str):assert (root/n).is_file() and sha(root/n)==h,(dep,n)
pr=W/'dependency-snapshots/geometry-point-derivation-instance-revision/primary';pn='Mathlib_Algebra_Polynomial_AlgebraMap.lean';v=(pr/pn).read_bytes();api=json.loads((pr/(pn+'.json')).read_text());assert base64.b64decode(api['content'])==v;assert hashlib.sha1(b'blob '+str(len(v)).encode()+b'\0'+v).hexdigest()==api['sha']=='d053dc25e14cfbce5f59b5fedef991473f30951a';assert 'ref=56a005855ea17e0b0958f73ec801ae140b0a1679' in api['url'];assert b'aeval (algebraMap R A x) p = algebraMap R A (p.eval x)' in v
for n in [pn,pn+'.json','NATIVE-PROVENANCE.json']:selected.append(str((pr/n).relative_to(W)))
H=c['head'];prefix='quartics/quartic-318-326/proof/experiments/'+c['predecessor_packet']+'/';assert not c['active'];assert len(c['unchanged_predecessor_sources'])==96
for n,h in c['unchanged_predecessor_sources'].items():
 v=subprocess.check_output(['git','show',H+':'+prefix+n],cwd=R);assert digest(v)==h;sources[Path(n).stem]=v
 for_keep=['DVRNormalizedAllPlaceCharts318.lean','DVRNormalizedFiniteOrder318.lean','DVRNormalizedInfinityOrder318.lean','DVRTwistSquareNormalization318.lean']
 if n in for_keep:
  d=S/'published-producers'/n;d.parent.mkdir(exist_ok=True);d.write_bytes(v)
order=c['proposed_order'];assert len(order)==len(set(order))==104;assert set(order)==set(sources);pos={n:i for i,n in enumerate(order)};external=set()
for n,v in sources.items():
 for line in v.decode().splitlines():
  ma=re.match(r'^(?:public )?import(?: all)? (\S+)\s*$',line)
  if not ma:continue
  dep=ma.group(1)
  if dep in pos:assert pos[dep]<pos[n],(n,dep)
  else:external.add(dep)
for n in j['sources']:
 text=(W/'sources'/n).read_text();code=re.sub(r'/\-.*?\-/','',text,flags=re.S);code=re.sub(r'--[^\n]*','',code);assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|set_option|public import all',code)
for n in selected:
 p=W/n;d=S/n;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,d)
(S/'ALL-OWNER-BINDINGS-VERIFIED.json').write_text(json.dumps(records,indent=2)+'\n');(S/'EXTERNAL-IMPORTS.json').write_text(json.dumps(sorted(external),indent=2)+'\n')
result={'status':'PASS_SOURCE_CURRENT_RESEARCH_CONTRACT_ONLY_NOT_HOSTED','application_sha256':sha(W/'APPLICATION.json'),'sources':j['sources'],'owner_bindings_verified':len(records),'obligations':9,'historical_published_roots':96,'inactive_ordered_roots':104,'internal_import_order_pass':True,'external_imports_not_new_packet_admission':sorted(external),'unchanged_adapter_bytes_during_dependency_update':True,'native_polynomial_blob':api['sha'],'local_lean_run':False,'source_bindings':{str(p.relative_to(B)):sha(p) for p in sorted(S.rglob('*')) if p.is_file()}}
(O/'NORMALIZED-EVALUATION-ADAPTER-CHECK.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS 2 unchanged adapter sources, 6 exact reviewed dependency sources, 1877 owner bindings, 9 research obligations, native polynomial API, 96 Git-exact historical roots / 104 inactive order; no Lean or packet admission')
