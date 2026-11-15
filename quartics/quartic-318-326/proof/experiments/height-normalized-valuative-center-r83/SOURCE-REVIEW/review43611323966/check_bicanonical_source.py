from pathlib import Path
import hashlib,json,subprocess,shutil,zipfile,re
B=Path('/workspace/scratch/41c6d5925c0e');W=B/'geometry-run43611323966';C=W/'candidates';O=B/'review43611323966';S=O/'bicanonical-source-snapshots';S.mkdir(exist_ok=True);R=B/'pel-integration43603177874/repo';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();n='IntegralOriginalBicanonicalRestrictions318';m=json.loads((C/(n+'-REPAIR.json')).read_text());H=m['head'];a=(C/(n+'.lean')).read_text();b=(C/(n+'.before')).read_text()
assert sha(C/(n+'.lean'))==m['candidate_sha256']=='f44a92128cd78998edbb10ee86acce8df7359380de8924ebd8c74cbdea25247f'
assert sha(C/(n+'.before'))==m['before_sha256']=='adefcb08f9717a19cb7b5d926415a74f5614c440a8542a8b47a4f034841452d6'
# Restore only the two explicitly delimited proof blocks; all remaining bytes must equal the published source.
x=a
for kind,nextline in [('branch','  rw [IntegralRationalBranchCoefficients318.scaled_coefficient,'),('infinity','  rw [IntegralRationalInfinityCoefficients318.scaled_coefficient,')]:
 anchor='theorem '+kind+'_restriction';ai=x.index(anchor);bi=b.index(anchor);start=x.index('  have transport :\n',ai);end=x.index(nextline,start);oldstart=b.index('  unfold '+kind+'Q\n',bi);oldend=b.index(nextline,oldstart);block=x[start:end]
 assert block.count('weightedSquare_restrict_to')==1 and block.endswith('  rw [transport]\n')
 assert '(R := ℚ)' in block and '(S := ' in block and '(T := ' in block
 x=x[:start]+b[oldstart:oldend]+x[end:]
assert x==b
root='quartics/quartic-318-326/proof/experiments/height-normalized-valuative-center-r69/'
assert b.encode()==subprocess.check_output(['git','show',H+':'+root+n+'.lean'],cwd=R)
for row in json.loads((C/'primary/PROVENANCE.json').read_text()):
 p=C/'primary'/row['path'];v=p.read_bytes();assert sha(p)==row['sha256'];assert hashlib.sha1(b'blob '+str(len(v)).encode()+b'\0'+v).hexdigest()==row['git_blob'];assert row['head']==H;assert v==subprocess.check_output(['git','show',H+':'+row['repository_path']],cwd=R)
A=W/'evidence/center';meta=json.loads((A/'ARTIFACT.json').read_text());assert meta['id']==m['own_artifact'] and meta['workflow_run']['id']==m['run'] and meta['workflow_run']['head_sha']==H;assert sha(A/'artifact.zip')==m['zip_sha256'] and meta['digest']=='sha256:'+m['zip_sha256']
with zipfile.ZipFile(A/'artifact.zip') as z:
 assert z.testzip() is None
 for fn in z.namelist():
  if not fn.endswith('/'):assert (A/'unpacked'/fn).read_bytes()==z.read(fn)
rp=A/'unpacked/progress-experiments/height-normalized-valuative-center-r69';assert (rp/'RESULT.json').read_bytes()==(C/'CENTER-RESULT.json').read_bytes();assert (rp/'logs'/(n+'.log')).read_bytes()==(C/(n+'.log')).read_bytes();assert sha(C/'CENTER-RESULT.json')==m['result_sha256'];assert sha(C/(n+'.log'))==m['log_sha256'];r=json.loads((C/'CENTER-RESULT.json').read_text());assert r['packet_sha256']==sha(C/'primary/intake.json');assert r['commands'][-1]=={'module':n,'exit_code':1,'seconds':10.287};assert all(v['exit_code']==0 for v in r['commands'][:-1]);log=(C/(n+'.log')).read_text();assert log.count('error: Tactic `rewrite` failed')==2 and ':93:6:' in log and ':112:6:' in log
files=[C/(n+'.lean'),C/(n+'.before'),C/(n+'.diff'),C/(n+'.log'),C/(n+'-REPAIR.json'),C/'CENTER-RESULT.json',A/'ARTIFACT.json']+list((C/'primary').iterdir())
for p in files:
 d=S/p.relative_to(W);d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,d)
extra={}
for mod in ['IntegralRationalFiniteAtlas318','IntegralInfinityOriginalField318','ContactIntrinsicFrames318','InfinityGlobalChart318','InfinityOpenChart318']:
 paths=subprocess.check_output(['git','ls-tree','-r','--name-only',H],cwd=R,text=True).splitlines();matches=[p for p in paths if p==root+mod+'.lean'];matches=matches or [p for p in paths if p=='quartics/quartic-318-326/proof/progress/'+mod+'.lean'];assert len(matches)==1,(mod,matches)
 v=subprocess.check_output(['git','show',H+':'+matches[0]],cwd=R);p=S/'additional-primary'/(mod+'.lean');p.parent.mkdir(exist_ok=True);p.write_bytes(v);extra[mod]={'repository_path':matches[0],'head':H,'sha256':sha(p),'git_blob':hashlib.sha1(b'blob '+str(len(v)).encode()+b'\0'+v).hexdigest()}
(S/'ADDITIONAL-PRIMARY.json').write_text(json.dumps(extra,indent=2)+'\n')
j={'status':'PASS_SOURCE_ONLY_NOT_HOSTED_ACCEPTANCE','module':n,'before_sha256':m['before_sha256'],'after_sha256':m['candidate_sha256'],'run':m['run'],'head':H,'artifact_id':m['own_artifact'],'zip_sha256':m['zip_sha256'],'observed_last_command':r['commands'][-1],'public_statements_declarations_options_maps_unchanged':True,'two_local_typed_transport_equalities':True,'source_bindings':{str(p.relative_to(B)):sha(p) for p in S.rglob('*') if p.is_file()},'local_lean_run':False}
(O/'BICANONICAL-SOURCE-CHECK.json').write_text(json.dumps(j,indent=2)+'\n');print('PASS exact two-block inverse; published before and 15 project/metadata primaries; own official-digest ZIP, exact RESULT/log/intake; no local Lean')
