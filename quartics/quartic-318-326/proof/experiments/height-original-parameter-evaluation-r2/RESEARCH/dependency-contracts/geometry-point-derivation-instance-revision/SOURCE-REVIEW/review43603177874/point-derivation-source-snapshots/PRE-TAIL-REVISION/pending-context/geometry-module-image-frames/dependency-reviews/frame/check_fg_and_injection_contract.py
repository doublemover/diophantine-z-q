from pathlib import Path
import json,hashlib,subprocess,re,shutil
B=Path('/workspace/scratch/41c6d5925c0e');O=B/'review43592150561';R=B/'pel-integration43592150561/repo';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();blob=lambda p:hashlib.sha1(b'blob '+str(p.stat().st_size).encode()+b'\0'+p.read_bytes()).hexdigest()
def snapshot(W,n,paths):
 S=O/'source-snapshots'/n
 for r in paths:
  p=W/r;q=S/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
 return {str(p.relative_to(O)):sha(p) for p in sorted(S.rglob('*')) if p.is_file()}
W=B/'geometry-fg-model-frames';a=json.loads((W/'APPLICATION.json').read_text());assert len(a['obligations'])==9
for r,h in a['bindings'].items():assert sha(W/r)==h,r
for row in a['obligations']:
 for k in ['required_input','constructed_input','justification']:assert row[k]
 for k in ['source_refs','evidence']:
  for r in row[k]:assert (W/r).is_file()
for row in json.loads((W/'primary/PROVENANCE.json').read_text()):
 p=W/'primary'/row['path'];assert row['commit']=='56a005855ea17e0b0958f73ec801ae140b0a1679';assert sha(p)==row['sha256'] and blob(p)==row['git_blob']
d=json.loads((W/'DEPENDENCY-PROVENANCE.json').read_text())
for row in d['project_primary']:
 p=W/row['path'];assert sha(p)==row['sha256'] and blob(p)==row['git_blob'];assert subprocess.check_output(['git','show',row['commit']+':'+row['repository_path']],cwd=R)==p.read_bytes()
for row in d['reviewed_research_dependencies']:assert (W/row['path']).read_bytes()==(B/row['original_bundle']/row['original_path']).read_bytes()
for r,h in d['previous_review_bindings'].items():assert sha(W/r)==h,r
f=json.loads((W/'FUTURE-CLOSURE.json').read_text());assert len(f['unchanged_predecessor_files'])==173 and f['closure_count']==178 and not f['active']
for n,row in f['unchanged_predecessor_files'].items():assert hashlib.sha256(subprocess.check_output(['git','show',f['base_commit']+':quartics/quartic-318-326/proof/experiments/'+f['base_packet']+'/'+n],cwd=R)).hexdigest()==row['sha256']
for p in (W/'sources').glob('*.lean'):
 text=re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S);assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',text)
paths=list(a['bindings'])+['APPLICATION.json','DEPENDENCY-PROVENANCE.json','FUTURE-CLOSURE.json','SUPPLEMENT-CHECK.log']
j={'status':'PASS_STANDALONE_SOURCE_AND_NINE_OBLIGATION_REVIEW','application_sha256':sha(W/'APPLICATION.json'),'sources':{p.name:sha(p) for p in (W/'sources').glob('*.lean')},'local_lean_run':False,'kernel_verified':False,'production_packet_review_complete':False,'source_bindings':snapshot(W,'geometry-fg-model-frames',paths)}
(O/'GEOMETRY-FG-SOURCE-CHECK.json').write_text(json.dumps(j,indent=2)+'\n');print('FG PASS two sources, nine standalone obligations, five native blobs, three exact project primaries, three reviewed research dependencies, 173 inherited Git source hashes; no Lean')
W=B/'replay-original-injectivity';j=json.loads((W/'RESEARCH-NINE-PART-CONTRACT.json').read_text());old=json.loads((O/'REPLAY-INJECTIVITY-SOURCE-BINDINGS.json').read_text());assert j['sources']==old['sources'];assert j['input_evaluation_sha256']==old['input_evaluation_sha256'];assert [r['id'] for r in j['obligations']]==list(range(1,10))
for n,h in j['sources'].items():assert sha(W/'candidates'/n)==h
for r,h in old['source_bindings'].items():assert sha(O/r)==h,r
x={'status':'PASS_RESEARCH_NINE_PART_CONTRACT_ADDENDUM_ONLY','contract_sha256':sha(W/'RESEARCH-NINE-PART-CONTRACT.json'),'sources':j['sources'],'prior_report_sha256':old['report_sha256'],'local_lean_run':False,'kernel_verified':False,'production_packet_review_complete':False,'source_bindings':snapshot(W,'injection-nine-contract',['RESEARCH-NINE-PART-CONTRACT.json'])}
(O/'REPLAY-INJECTIVITY-NINE-CONTRACT-CHECK.json').write_text(json.dumps(x,indent=2)+'\n');print('Injection PASS exact four source identities and immutable earlier review; nine standalone semantic boundaries; no operational packet or kernel acceptance')
