from pathlib import Path
import json,hashlib,subprocess,zipfile,shutil
B=Path('/workspace/scratch/41c6d5925c0e');O=B/'review43592150561';W=B/'picard-run43592150561';R=B/'pel-integration43586414080/repo';H='75be14ed25ed39f46289f1c69914810afd46068c';X='quartics/quartic-318-326/proof/experiments/original-five-kernel-norm-equivalence-r18';P=W/'predecessors/original-five-kernel-norm-equivalence-r18';N='OriginalDualAlgebraNormTrace318';A=W/'candidates/five'/f'{N}.lean';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();before=subprocess.check_output(['git','show',H+':'+X+'/'+N+'.lean'],cwd=R);assert before==(P/(N+'.lean')).read_bytes();after=A.read_bytes();assert sha(A)=='beb08f2c3e2c97dd5715dcc874293360205e88dd75a34c0e9c77f1a9b897bce7'
old='''  rw [← hx, Algebra.norm_eq_of_algEquiv (equivalence R S) (x ⊗ₜ[R] 1),
    OriginalRightTensorNormTrace318.norm_coefficient,
    TrivSqZeroExt.algebraMap_eq_inl]'''
new='''  calc
    Algebra.norm (DualNumber R) (inl x : DualNumber S) =
        Algebra.norm (DualNumber R) (equivalence R S (x ⊗ₜ[R] 1)) :=
      congrArg (Algebra.norm (DualNumber R)) hx.symm
    _ = Algebra.norm (DualNumber R) (x ⊗ₜ[R] (1 : DualNumber R)) :=
      Algebra.norm_eq_of_algEquiv (R := DualNumber R) (equivalence R S) (x ⊗ₜ[R] 1)
    _ = inl (Algebra.norm R x) := by
      rw [OriginalRightTensorNormTrace318.norm_coefficient,
        TrivSqZeroExt.algebraMap_eq_inl]'''
assert before.decode().count(old)==1 and before.decode().replace(old,new).encode()==after
art=next(x for x in json.loads((O/'INDEPENDENT-GITHUB-ARTIFACTS-DIAGNOSTICS.json').read_text())['artifacts'] if x['id']==14113377247);assert art['workflow_run']['head_sha']==H and art['workflow_run']['id']==43592150561;z=W/'evidence/five-r18.zip';assert sha(z)==art['digest'].removeprefix('sha256:')
with zipfile.ZipFile(z) as zz:
 assert zz.testzip() is None
 for n in zz.namelist():
  if not n.endswith('/'):assert zz.read(n)==(z.with_suffix('')/n).read_bytes()
E=z.with_suffix('')/'progress-experiments/original-five-kernel-norm-equivalence-r18';res=json.loads((E/'RESULT.json').read_text());assert res['packet_sha256']==sha(P/'intake.json') and res['status']=='FAILED';assert res['commands'][-1]['module']==N and res['commands'][-1]['exit_code']==1
assert subprocess.check_output(['git','show',H+':'+X+'/intake.json'],cwd=R)==(P/'intake.json').read_bytes()
S=O/'source-snapshots/picard-five';S.mkdir(parents=True,exist_ok=True)
def save(p,n):shutil.copy2(p,S/n)
(S/'before.lean').write_bytes(before);save(A,'after.lean');save(A.with_suffix('.lean.patch'),'source.patch');save(E/'RESULT.json','RESULT.json');save(E/'logs'/f'{N}.log',f'{N}.log');save(P/'intake.json','intake.json');save(O/'PINNED-NORM-EQUIVALENCE.json','PINNED-NORM-EQUIVALENCE.json')
for n in ['OriginalRightTensorNormTrace318','DualNumberScalarExtension318','OriginalFiniteFreeDualTransfer318','ActualDualUnitNormIdentification318']:
 data=subprocess.check_output(['git','show',H+':'+X+'/'+n+'.lean'],cwd=R);assert data==(P/(n+'.lean')).read_bytes();(S/(n+'.lean')).write_bytes(data)
r={'status':'PASS_CANDIDATE_SOURCE_ONLY','before_sha256':hashlib.sha256(before).hexdigest(),'after_sha256':sha(A),'run':43592150561,'head':H,'artifact':art,'public_statements_definitions_options_unchanged':True,'local_lean_run':False,'candidate_hosted_pass':False,'new_packet_contract_reviewed':False,'source_bindings':{str(p.relative_to(O)):sha(p) for p in S.iterdir() if p.is_file()}};(O/'PICARD-FIVE-SOURCE-CHECK.json').write_text(json.dumps(r,indent=2)+'\n');print('PASS exact calc-only norm_inl delta, authentic own artifact, original right-action/equivalence/direct consumers')
