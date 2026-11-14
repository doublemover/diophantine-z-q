from pathlib import Path
import json,hashlib,subprocess,zipfile,shutil
B=Path('/workspace/scratch/41c6d5925c0e');W=B/'picard-run43603177874';O=B/'review43603177874';R=B/'pel-integration43597228569/repo';H='57227e167abe49436d651b932ff75d5bdf9b5898';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for lane,n,packet,expected,native,consumers in [
 ('gluing','ContactCoefficientRestrictionSquares318','relative-original-normalized-kernel-gluing-r16','3d46e39faea16541608a7bc9d9480722f0c8dd47c2f9a1382bdda0aee1aa4e84','Tilde.lean',['ContactCoefficientCechBaseChange318']),
 ('five','DualUnitFactorization318','original-five-kernel-norm-equivalence-r20','6199358cd87d2a4947db1175a8c39548117f85f955b16b445a8bcd15176a2373','TrivSqZeroExt.Basic.lean',['DualUnitNormConstruction318','OriginalOpenDualCoordinates318'])]:
 S=O/('picard-'+lane+'-source-snapshots');S.mkdir(exist_ok=True);P=W/'source-snapshots'/lane;C=W/'candidates';A=W/'raw'/lane;rel='quartics/quartic-318-326/proof/experiments/'+packet
 before=P/(n+'.lean');after=C/(n+'.lean');a=after.read_text();b=before.read_text();assert sha(after)==expected;assert before.read_bytes()==subprocess.check_output(['git','show',H+':'+rel+'/'+n+'.lean'],cwd=R)
 if lane=='gluing':assert a.count('    moduleSpecΓFunctor,modulesSpecToSheaf,\n')==2 and a.replace('    moduleSpecΓFunctor,modulesSpecToSheaf,\n','')==b
 else:
  x=a.replace('  change (1 + TrivSqZeroExt.inr a : Dual R).fst = 1\n  simp\n','  simp [coefficient, unit, DualNumberScheme318.reductionRing]\n').replace("  map_mul' z w := by\n    simp only [map_mul, mul_inv_rev]\n    ac_rfl\n","  map_mul' z w := by simp [mul_comm, mul_left_comm, mul_assoc]\n");assert x==b
 for p in P.glob('*.lean'):
  if p.name==native:continue
  assert p.read_bytes()==subprocess.check_output(['git','show',H+':'+rel+'/'+p.name],cwd=R)
 assert (P/'intake.json').read_bytes()==subprocess.check_output(['git','show',H+':'+rel+'/intake.json'],cwd=R)
 m=json.loads((P/(native+'.GITHUB-RECEIPT.json')).read_text());v=(P/native).read_bytes();obj=hashlib.sha1(b'blob '+str(len(v)).encode()+b'\0'+v).hexdigest();assert m['ref']=='56a005855ea17e0b0958f73ec801ae140b0a1679' and m['blob_sha']==obj and m['sha256']==sha(P/native);assert m['official_response']['content'].encode()==v
 meta=json.loads((A/'ARTIFACT.json').read_text());assert meta['workflow_run']['head_sha']==H and meta['workflow_run']['id']==43603177874 and meta['digest']=='sha256:'+sha(A/'artifact.zip')
 with zipfile.ZipFile(A/'artifact.zip') as z:
  assert z.testzip() is None
  for fn in z.namelist():
   if not fn.endswith('/'):assert (A/fn).read_bytes()==z.read(fn)
 rp=A/'progress-experiments'/packet;r=json.loads((rp/'RESULT.json').read_text());assert r['packet_sha256']==sha(P/'intake.json');assert r['commands'][-1]['module']==n and r['commands'][-1]['exit_code']==1 and all(x['exit_code']==0 for x in r['commands'][:-1]);log=(rp/'logs'/(n+'.log')).read_text();assert log.count('error:')==2
 for p in [after,W/('DIFF-'+lane+'.patch'),A/'ARTIFACT.json',rp/'RESULT.json',rp/'logs'/(n+'.log')]+list(P.iterdir()):
  if p.is_file():
   dest=S/p.relative_to(W);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dest)
 for consumer in consumers:(S/(consumer+'.lean')).write_bytes(subprocess.check_output(['git','show',H+':'+rel+'/'+consumer+'.lean'],cwd=R))
 j={'status':'PASS_CANDIDATE_SOURCE_ONLY_CURRENT_PACKET_CONTRACT_PENDING','module':n,'before_sha256':sha(before),'after_sha256':sha(after),'run':43603177874,'head':H,'artifact_id':meta['id'],'artifact_zip_sha256':sha(A/'artifact.zip'),'intake_sha256':sha(P/'intake.json'),'observed_final_command':r['commands'][-1],'native_git_blob':obj,'source_bindings':{str(p.relative_to(B)):sha(p) for p in S.rglob('*') if p.is_file()},'local_lean_run':False}
 (O/('PICARD-'+lane.upper()+'-SOURCE-CHECK.json')).write_text(json.dumps(j,indent=2)+'\n');print('PASS',lane,expected,'own ZIP/intake/Git/native blob; exact narrow inverse')
