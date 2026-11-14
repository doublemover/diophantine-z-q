from pathlib import Path
import json,hashlib,subprocess,re,shutil,zipfile
B=Path('/workspace/scratch/41c6d5925c0e');R=B/'pel-integration43586414080/repo';O=B/'review43592150561';HEAD='75be14ed25ed39f46289f1c69914810afd46068c';REL='quartics/quartic-318-326/proof/experiments/relative-original-normalized-kernel-gluing-r14';P=R/REL;N='OriginalLineSquareSections318';A=B/'picard-run43592150561/candidates/gluing'/f'{N}.lean';E=B/'picard-run43592150561/evidence/gluing-r14/progress-experiments/relative-original-normalized-kernel-gluing-r14';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before=subprocess.check_output(['git','show',HEAD+':'+REL+'/'+N+'.lean'],cwd=R);assert before==(P/(N+'.lean')).read_bytes();after=A.read_bytes();assert sha(A)=='d04930069ec1605ef81cab80b921529f77f63389abe601ddae9cdb46d7aa869f'
assert before.split(b':= by',1)[0]==after.split(b':= by',1)[0];assert re.findall(rb'^\s*set_option\s+.*$',before,re.M)==re.findall(rb'^\s*set_option\s+.*$',after,re.M)
expected=before.decode().replace('Category.comp_id,Category.assoc] using','Category.comp_id,Category.id_comp,Category.assoc] using')
expected=expected.replace('      rw [naturality]','''      exact congrArg
        (fun t => ((comparison b j j' p hb).hom.app M).app ⊤ t)
        (OriginalSectionPullbackComposition318.naturality b
          ((PullbackPathComposition318.iso e i j h).hom.app M)
          (pull e ((Scheme.Modules.pullback i).obj M) s)).symm''')
expected=expected.replace('    _ = _ := by rw [hs,naturality]','''    _ = _ := by
      rw [hs]
      exact congrArg
        (fun t => ((PullbackPathComposition318.iso e' i' j' h').hom.app
          ((Scheme.Modules.pullback p).obj M)).app ⊤ t)
        (OriginalSectionPullbackComposition318.naturality e'
          ((comparison a i i' p ha).hom.app M)
          (pull a ((Scheme.Modules.pullback i).obj M) s))''')
assert expected.encode()==after
art=next(x for x in json.loads((O/'INDEPENDENT-GITHUB-ARTIFACTS.json').read_text())['artifacts'] if x['id']==14113485810);assert art['workflow_run']['head_sha']==HEAD and art['workflow_run']['id']==43592150561
z=B/'picard-run43592150561/evidence/gluing-r14.zip';assert sha(z)==art['digest'].removeprefix('sha256:')
with zipfile.ZipFile(z) as zz:
 assert zz.testzip() is None
 for f in zz.namelist():
  if not f.endswith('/'):assert zz.read(f)==(z.with_suffix('')/f).read_bytes()
result=json.loads((E/'RESULT.json').read_text());assert result['packet_sha256']==sha(P/'intake.json') and result['status']=='FAILED';assert result['commands'][-1]['module']==N and result['commands'][-1]['exit_code']==1
cmd={x['module']:x for x in result['commands']};assert cmd['OriginalPullbackSquarePasting318']['exit_code']==cmd['OriginalSectionPullbackComposition318']['exit_code']==0
S=O/'source-snapshots/picard-gluing';S.mkdir(parents=True,exist_ok=True);(S/'before.lean').write_bytes(before);shutil.copy2(A,S/'after.lean')
files=[E/'RESULT.json',E/'logs'/f'{N}.log',A.with_suffix('.lean.patch'),P/'intake.json']
for f in files:shutil.copy2(f,S/f.name)
for n in ['OriginalSectionPullbackComposition318','OriginalPullbackSquarePasting318','ContactCoefficientRestrictionSquares318','OriginalAffinePathWholeSections318','ContactCoefficientLineCharts318']:
 raw=subprocess.check_output(['git','show',HEAD+':'+REL+'/'+n+'.lean'],cwd=R);assert raw==(P/(n+'.lean')).read_bytes();(S/(n+'.lean')).write_bytes(raw)
r={'module':N,'before_sha256':hashlib.sha256(before).hexdigest(),'after_sha256':sha(A),'head':HEAD,'run':43592150561,'own_artifact':art,'result_sha256':sha(E/'RESULT.json'),'log_sha256':sha(E/'logs'/f'{N}.log'),'predecessor_intake_sha256':sha(P/'intake.json'),'public_statement_unchanged':True,'options_imports_unchanged':True,'new_hypotheses':False,'local_lean_run':False,'review_scope':'CANDIDATE_SOURCE_ONLY_NOT_NEW_PACKET_CONTRACT','source_snapshots':{str(f.relative_to(O)):sha(f) for f in S.rglob('*') if f.is_file()}}
(O/'PICARD-GLUING-SOURCE-CHECK.json').write_text(json.dumps(r,indent=2)+'\n');print('PASS exact3 proof changes, authentic own evidence, producer and consumer Git bytes')
