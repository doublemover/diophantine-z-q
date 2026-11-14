from pathlib import Path
import json,hashlib,subprocess,shutil,re,zipfile
B=Path('/workspace/scratch/41c6d5925c0e');O=B/'review43597228569';R=B/'pel-integration43592150561/repo';H='2af419e128047c483b3cdc0ba5e4d65c09d7c4ce';X='quartics/quartic-318-326/proof/experiments/'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
configs=[('GEOMETRY-FIVECHART','geometry-run43597228569','height-normalized-valuative-center-r67','IntegralRationalFiveChartGeometry318',14114643980,['IntegralRationalGlobalComparison318','IntegralRationalFullOverlap318','IntegralOriginalBicanonicalRestrictions318','IntegralOriginalGlobalPair318']),('PICARD-GLUING','picard-run43597228569','relative-original-normalized-kernel-gluing-r15','ContactCoefficientRestrictionSquares318',14115500355,['ContactOriginalRelativeLineOverlap318','ContactOriginalRelativeOverlap318','OriginalLineAffineModel318','LineSheafPullback318','OriginalLineSquareSections318','ContactCoefficientCechBaseChange318']),('PICARD-FIVE','picard-run43597228569','original-five-kernel-norm-equivalence-r19','OriginalDualAlgebraNormTrace318',14115187935,['OriginalRightTensorNormTrace318','DualNumberScalarExtension318','OriginalKernelNormTraceEquivalence318'])]
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',H,'--','quartics/quartic-318-326/proof'],cwd=R).decode().splitlines()
for tag,work,packet,n,aid,prim in configs:
 W=B/work;S=O/'source-snapshots'/tag.lower();S.mkdir(parents=True,exist_ok=True)
 def save(p,r):
  q=S/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
 before=subprocess.check_output(['git','show',H+':'+X+packet+'/'+n+'.lean'],cwd=R).decode();p=W/'candidates'/(n+'.lean');after=p.read_text();save(p,'after/'+p.name);(S/'before.lean').write_text(before)
 if tag=='GEOMETRY-FIVECHART':
  assert after==before.replace('  apply CommRingCat.hom_ext\n  apply RingHom.ext\n  exact branchEquiv_source c i\n','')
  art=W/'evidence/center-artifact.json';z=W/'evidence/center.zip';E=W/'evidence/center';save(W/'candidates'/(n+'-REPAIR.json'),'REPAIR.json')
 elif tag=='PICARD-GLUING':
  exp=before
  for side in ['finite','infinity']:
   old=f'    ContactOriginalRelativeLineOverlap318.{side}Comparison,\n';new=old+f'    ContactOriginalRelativeLineOverlap318.{side}Arrow,\n    ContactOriginalRelativeLineOverlap318.{side}Line,\n    ContactOriginalRelativeOverlap318.{side}Edge,\n    OriginalLineAffineModel318.sections,LineSheafPullback318.line,\n';exp=exp.replace(old,new)
  assert after==exp;art=W/'raw/gluing/ARTIFACT.json';z=W/'raw/gluing'/f'artifact-{aid}.zip';E=W/'raw/gluing/extracted'
 else:
  assert after==before.replace('      Algebra.norm_eq_of_algEquiv (R := DualNumber R) (equivalence R S) (x ⊗ₜ[R] 1)','      Algebra.norm_eq_of_algEquiv (R := DualNumber R) (equivalence R S)\n        (x ⊗ₜ[R] (1 : DualNumber R))')
  art=W/'raw/five/ARTIFACT.json';z=W/'raw/five'/f'artifact-{aid}.zip';E=W/'raw/five/extracted'
 assert re.findall(r'^.*(?:import|set_option).*$',before,re.M)==re.findall(r'^.*(?:import|set_option).*$',after,re.M)
 A=json.loads(art.read_text());assert A['id']==aid and A['workflow_run']['id']==43597228569 and A['workflow_run']['head_sha']==H and A['digest']=='sha256:'+sha(z)
 with zipfile.ZipFile(z) as zz:
  assert zz.testzip() is None
  for name in zz.namelist():
   if not name.endswith('/'):assert zz.read(name)==(E/name).read_bytes()
 ep=E/'progress-experiments'/packet;J=json.loads((ep/'RESULT.json').read_text());assert J['commands'][-1]['module']==n and J['commands'][-1]['exit_code']==1
 it=subprocess.check_output(['git','show',H+':'+X+packet+'/intake.json'],cwd=R);assert hashlib.sha256(it).hexdigest()==J['packet_sha256'];(S/'predecessor-intake.json').write_bytes(it)
 for f in [art,ep/'RESULT.json',ep/'logs'/(n+'.log')]:save(f,'evidence/'+f.name)
 pr=[]
 for name in prim:
  poss=[p for p in paths if p.endswith('/'+name+'.lean')];chosen=next((p for p in poss if p==X+packet+'/'+name+'.lean'),next((p for p in poss if '/progress/' in p),None))
  assert chosen,name
  data=subprocess.check_output(['git','show',H+':'+chosen],cwd=R);q=S/'primary'/(name+'.lean');q.parent.mkdir(exist_ok=True);q.write_bytes(data);pr.append({'path':chosen,'sha256':sha(q)})
 result={'status':'PASS_CANDIDATE_SOURCE_ONLY','run':43597228569,'head':H,'module':n,'before_sha256':hashlib.sha256(before.encode()).hexdigest(),'after_sha256':sha(p if False else W/'candidates'/(n+'.lean')),'own_artifact':aid,'primary_git_sources':pr,'public_statements_and_options_unchanged':True,'local_lean_run':False,'candidate_hosted_pass':False,'packet_contract_review_complete':False,'source_bindings':{str(f.relative_to(O)):sha(f) for f in S.rglob('*') if f.is_file()}}
 (O/(tag+'-SOURCE-CHECK.json')).write_text(json.dumps(result,indent=2)+'\n');print(tag,'PASS exact observed delta,own artifact,published before/intake,primary producers/consumers; no Lean')
