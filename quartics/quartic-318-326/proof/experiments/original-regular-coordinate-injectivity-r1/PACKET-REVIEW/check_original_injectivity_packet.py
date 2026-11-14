from pathlib import Path
import sys,json,hashlib,re,subprocess,shutil
sys.dont_write_bytecode=True
B=Path('/workspace/scratch/41c6d5925c0e');O=B/'review43597228569';R=B/'pel-integration43592150561/repo';W=B/'picard-original-evaluation-experiment';N='original-regular-coordinate-injectivity-r1';P=W/'experiments'/N;U=B/'pel-run43597228569/successors/pel-original-character-ordered-biholomorph-r17';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();sys.path.insert(0,str(R/'scripts'));import check_progress_experiment as ce
assert sha(P/'APPLICATION.json')=='ecbd1f90a160159ce641326c6710b15543f6eb6d7fd759454ac0b9169d659880';assert sha(P/'intake.json')=='959550051c8159e302b4f87a0878a4c951ec5c6adb243275bc5cc99f3db32604';assert sha(P/'README.md')=='0590941fbd1745cad440e5b8606952c71a8ae964fe821ecad0b4c70f4437b7d9'
a=json.loads((P/'APPLICATION.json').read_text());d=json.loads((P/'intake.json').read_text());pr=json.loads((P/'PROVENANCE.json').read_text());ud=json.loads((U/'intake.json').read_text());plan=ce.ci.derive_plan();assert len(plan['module_order'])==1837
assert sha(U/'APPLICATION.json')==pr['future_upstream_application_sha256']=='d613a81c344c299bc7e5e6f9887220fd1a53fdce60b256b3c1c0ca29cadff803';assert sha(U/'intake.json')==pr['future_upstream_intake_sha256'];assert (P/'UPSTREAM/APPLICATION.json').read_bytes()==(U/'APPLICATION.json').read_bytes();assert (P/'UPSTREAM/intake.json').read_bytes()==(U/'intake.json').read_bytes()
new=a['new_sources'];assert len(new)==5 and a['changed_sources']=={};assert set(d['new_modules'])=={Path(n).stem for n in new};assert set(d['files'])==set(a['sources'])=={p.name for p in P.glob('*.lean')};assert len(d['files'])==489
needed=set();base=set();state={};order=[]
def visit(n):
 if n in plan['module_keys']:base.add(n);return
 if n.split('.')[0] in ce.OFFICIAL_PREFIXES:return
 assert n+'.lean' in d['files'],n
 assert state.get(n)!=1,('cycle',n)
 if state.get(n)==2:return
 state[n]=1;needed.add(n)
 for dep in sorted(ce.ci.import_names((P/(n+'.lean')).read_text())):visit(dep)
 state[n]=2;order.append(n)
for n in sorted(Path(x).stem for x in new):visit(n)
assert order==d['order'] and needed==set(d['order']);assert ce.required_baseline(plan,base)==pr['baseline_order'] and len(pr['baseline_order'])==73
for n in d['order']:
 p=P/(n+'.lean');h=sha(p);assert d['files'][p.name]['sha256']==a['sources'][p.name]==h;assert sorted(ce.ci.import_names(p.read_text()))==d['files'][p.name]['imports'];row=pr['sources'][n];assert h==row['sha256'] and (B/row['path']).read_bytes()==p.read_bytes()
 if p.name not in new:assert p.read_bytes()==(U/p.name).read_bytes();assert h==ud['files'][p.name]['sha256']
assert len(d['unchanged_upstream_modules'])==484 and set(d['unchanged_upstream_modules'])==needed-{Path(n).stem for n in new}
for fn,h in a['bindings'].items():assert sha(P/fn)==h,fn
assert len(a['obligations'])==9
for row in a['obligations']:
 for k in ['required_input','constructed_input','justification','source_references','evidence']:assert row[k]
 for ref in row['source_references']+row['evidence']:assert (P/ref.split(':',1)[0]).is_file()
old=B/'review43592150561';manifest_names=['PICARD-REGULAR-EVALUATION-SOURCE-BINDINGS.json','REPLAY-INJECTIVITY-SOURCE-BINDINGS.json','REPLAY-INJECTIVITY-NINE-CONTRACT-BINDINGS.json'];allfiles={str(p.relative_to(P)):sha(p) for p in P.rglob('*') if p.is_file()}
for name in manifest_names:
 m=json.loads((old/name).read_text());assert sha(old/name) in a['bindings'].values()
 for ref,h in m['source_bindings'].items():assert sha(old/ref)==h and any(v==h and k in a['bindings'] for k,v in allfiles.items()),(name,ref)
expected={**json.loads((old/'REPLAY-INJECTIVITY-SOURCE-BINDINGS.json').read_text())['sources'],'PELOriginalRegularCoordinateAlgebra318.lean':'999346f585c82c2c94f6f4a9f477bd352281af695caf7c272561e41e99a9aaad'};assert new==expected
for flag in ['local_lean_run','kernel_verified','independent_acceptance','full_arithmetic_theorem_proved','upstream_publication_verified','current_packet_review_complete']:assert a[flag] is False
assert 'No pass of upstream' in (P/'README.md').read_text() and 'may stop on an upstream frontier' in (P/'README.md').read_text();ce.packet(N,plan,W/'experiments')
S=O/'research-packet-snapshots'/N;S.mkdir(parents=True,exist_ok=True)
for n in ['APPLICATION.json','intake.json','README.md','PROVENANCE.json','UPSTREAM/APPLICATION.json','UPSTREAM/intake.json']+list(new):
 q=S/n;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(P/n,q)
j={'status':'PASS_CURRENT_PACKET_SOURCE_CONTRACT_CLOSURE_ONLY_UPSTREAM_PUBLICATION_GATE_PENDING','packet':N,'application_sha256':sha(P/'APPLICATION.json'),'intake_sha256':sha(P/'intake.json'),'readme_sha256':sha(P/'README.md'),'provenance_sha256':sha(P/'PROVENANCE.json'),'root_count':489,'new_sources':new,'upstream_count':484,'upstream_application_sha256':sha(U/'APPLICATION.json'),'upstream_intake_sha256':sha(U/'intake.json'),'baseline_count':73,'baseline_order':pr['baseline_order'],'full_root_order':order,'source_sha256':a['sources'],'application_bindings':a['bindings'],'obligations':a['obligations'],'all_source_review_companions_exact':True,'native_packet_check':'PASS','local_lean_run':False,'kernel_verified':False,'upstream_publication_verified':False,'final_publication_index_review_complete':False,'reviewer_evidence':{str(p.relative_to(O)):sha(p) for p in sorted(S.rglob('*')) if p.is_file()}}
(O/'ORIGINAL-INJECTIVITY-PACKET-CHECK.json').write_text(json.dumps(j,indent=2)+'\n');print('PASS exact5 reviewed new sources +484 exact frozen upstream closure +73 baseline dependencies; nine current obligations, all source companions, native packet/static guards. Actual upstream publication gate and final index pending; no Lean.')
