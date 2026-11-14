from pathlib import Path
import subprocess,hashlib,json,difflib,shutil
B=Path(__file__).resolve().parent;C=B/'candidates';R=B.parent/'followup-integration43592150561/repo';HEAD='2b151fc62f5872fd569489336d35f536d4cae0a4';old='height-normalized-valuative-center-r66';root='quartics/quartic-318-326/proof/experiments/'+old;M='IntegralRationalFiveChartGeometry318';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();W=lambda p,d:p.write_text(json.dumps(d,indent=2)+'\n')
raw=subprocess.check_output(['git','show',HEAD+':'+root+'/'+M+'.lean'],cwd=R);(C/(M+'.lean.before')).write_bytes(raw)
s=raw.decode();target='  change Spec.map (branchEquiv c i).toRingEquiv.toCommRingCatIso.hom ≫ _ = _\n';replacement='  change Spec.map (branchEquiv c i).toRingEquiv.toCommRingCatIso.hom ≫ _ =\n    _ ≫ Spec.map (IntegralRationalFullOverlap318.sourceEquiv c).toRingEquiv.toCommRingCatIso.hom\n';assert s.count(target)==1;s=s.replace(target,replacement);(C/(M+'.lean')).write_text(s);(C/(M+'.lean.diff')).write_text(''.join(difflib.unified_diff(raw.decode().splitlines(keepends=True),s.splitlines(keepends=True),fromfile=M+'.lean.before',tofile=M+'.lean')))
E=B/'evidence/center/progress-experiments'/old;shutil.copyfile(E/'RESULT.json',C/'center-RESULT.json');shutil.copyfile(E/'logs'/(M+'.log'),C/(M+'.log'))
intake=subprocess.check_output(['git','show',HEAD+':'+root+'/intake.json'],cwd=R);(C/'predecessor-intake.json').write_bytes(intake);r=json.loads((C/'center-RESULT.json').read_text());assert r['packet_sha256']==H(C/'predecessor-intake.json');assert [(x['module'],x['exit_code']) for x in r['commands'][-3:]]==[('IntegralRationalBranchCoefficients318',0),('IntegralRationalInfinityCoefficients318',0),(M,1)]
primary=['IntegralRationalGlobalComparison318','IntegralRationalFiniteAtlas318','IntegralRationalFullOverlap318','IntegralOriginalBicanonicalRestrictions318','IntegralOriginalGlobalPair318','ContactIntrinsicFrames318','IntegralGluedDifferentialFrames318'];prov=[]
for m in primary:
 for path in [root+'/'+m+'.lean','quartics/quartic-318-326/proof/progress/'+m+'.lean']:
  q=subprocess.run(['git','show',HEAD+':'+path],cwd=R,capture_output=True)
  if q.returncode==0:
   out=C/'primary'/(m+'.lean');out.write_bytes(q.stdout);prov.append({'head':HEAD,'path':path,'sha256':H(out)});break
 else:raise AssertionError(m)
W(C/'primary/PROVENANCE.json',prov)
repair={'module':M,'run':43593737114,'head':HEAD,'artifact':14113449077,'before_sha256':H(C/(M+'.lean.before')),'candidate_sha256':H(C/(M+'.lean')),'own_result_sha256':H(C/'center-RESULT.json'),'predecessor_intake_sha256':H(C/'predecessor-intake.json'),'observed_log_sha256':H(C/(M+'.log')),'diagnostic':'At28:21 the second reverse Spec.map_comp rewrite fails because the RHS still contains finiteIso.inv rather than an exposed Spec.map. The first left rewrite succeeded.','change':'Expose only the same native RHS sourceEquiv Spec map in the existing change; all remaining proof steps and public statements stay unchanged.','status':'SOURCE_REVIEW_AND_HOSTED_REPLAY_PENDING','public_statement_changed':False,'helper_added':False,'options_changed':False,'local_lean_run':False};W(C/(M+'-REPAIR.json'),repair);print(json.dumps(repair,indent=2))
