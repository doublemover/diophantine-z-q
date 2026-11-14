import pathlib, json, hashlib, subprocess, zipfile, re, shutil
root=pathlib.Path('/workspace/scratch/41c6d5925c0e'); out=root/'review43586414080'; repo=root/'pel-integration43582938856/repo'; head='f89bd0a3cb8a788d6c7f2f494a21d7d103a893cb'; exp='quartics/quartic-318-326/proof/experiments/'
h=lambda b:hashlib.sha256(b).hexdigest()
records=json.loads((out/'INDEPENDENT-GITHUB-PRIMARY-RECORDS.json').read_text()); arts=json.loads((out/'NEXT-INDEPENDENT-ARTIFACTS.json').read_text())['structuredContent']['artifacts']
files={}
def git(path):return subprocess.check_output(['git','show',head+':'+path],cwd=repo)
def put(case,name,data):
 p=out/'source-snapshots'/case/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);return str(p.relative_to(out))
def evidence(case,packet,archive,extracted,module):
 a=next(a for a in arts if a['name']=='experiment-'+packet);assert a['workflow_run']['id']==43586414080 and a['workflow_run']['head_sha']==head
 assert h(archive.read_bytes())==a['digest'].split(':')[1]
 result=extracted/'RESULT.json';log=extracted/'logs'/(module+'.log')
 z=zipfile.ZipFile(archive)
 for p in [result,log]:
  match=[n for n in z.namelist() if n.endswith('/'+packet+'/'+p.relative_to(extracted).as_posix())];assert len(match)==1;assert z.read(match[0])==p.read_bytes();put(case,packet+'/'+p.relative_to(extracted).as_posix(),p.read_bytes())
 r=json.loads(result.read_text());intake=git(exp+packet+'/intake.json');assert r['packet_sha256']==h(intake)
 assert r['commands'][-1]['module']==module and r['commands'][-1]['exit_code']!=0
 put(case,packet+'/predecessor-intake.json',intake);put(case,packet+'/ARTIFACT.json',(json.dumps(a,indent=2)+'\n').encode())
 return {'artifact_id':a['id'],'packet':packet,'zip_sha256':h(archive.read_bytes()),'result_sha256':h(result.read_bytes()),'log_sha256':h(log.read_bytes()),'intake_sha256':h(intake),'last_command':r['commands'][-1]}
def source(case,packet,module,after):
 before=git(exp+packet+'/'+module+'.lean');aa=after.read_bytes();put(case,'before.lean',before);put(case,'after.lean',aa)
 assert re.findall(rb'^set_option .*$',before,re.M)==re.findall(rb'^set_option .*$',aa,re.M)
 assert re.findall(rb'^.*import .*$',before,re.M)==re.findall(rb'^.*import .*$',aa,re.M)
 return before.decode(),aa.decode(),{'module':module,'candidate_path':str(after),'before_sha256':h(before),'after_sha256':h(aa)}
def snapshot_git(case,packet,module):put(case,module+'.lean',git(exp+packet+'/'+module+'.lean'))
newrecords=json.loads((out/'NEXT-INDEPENDENT-PRIMARY-RECORDS.json').read_text())
def source_at(case,path):
 # Exact repository primary producer/consumer, without treating evidence as a module shadow.
 data=path.read_bytes();name=path.name
 candidates=subprocess.check_output(['git','ls-tree','-r','--name-only',head,'--','quartics/quartic-318-326/proof'],cwd=repo).decode().splitlines()
 paths=[x for x in candidates if x.endswith('/'+name)]
 assert any(git(x)==data for x in paths),name
 put(case,'primary/'+name,data)
# Arithmetic positive.
case='arithmetic-positive';base=root/'arithmetic-run43586414080';module='ContactOriginalCohomologyCoordinates318';packet='contact-original-positive-generators-r74'
b,a,s=source(case,packet,module,base/'candidates'/(module+'.lean'))
expected=b.replace('AddEquiv.apply_symm_apply]\n','AddEquiv.apply_symm_apply,LinearEquiv.coe_toAddEquiv]\n').replace('lemma boundary_surjective : Function.Surjective (boundaryLinear c L) :=\n  (OriginalLineMayerVietorisQuotient318.boundary_surjective L','lemma boundary_surjective : Function.Surjective (boundaryLinear c L) := by\n  letI : IsIntegral (ContactProjectiveModel318.model c) :=\n    ContactProjectiveModel318.model_integral c\n  exact (OriginalLineMayerVietorisQuotient318.boundary_surjective L')
assert a==expected
s['evidence']=[evidence(case,packet,base/'positive.zip',base/'positive-logs/progress-experiments'/packet,module)]
for n in ['ContactOriginalLaurentBoundary318','OriginalLineMayerVietorisQuotient318','OriginalLineRationalCohomology318','ContactProjectiveModel318','ContactOriginalWholeRestriction318','ContactOriginalRestrictionCoordinates318','ContactIntrinsicDifferentials318','ContactOriginalLineHOneFinite318','ContactOriginalLineSectionsFinite318']:source_at(case,base/'candidates/primary'/(n+'.lean'))
p=base/'candidates/primary/Mathlib-Algebra-Module-Equiv-Defs.lean';raw=p.read_bytes();assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==newrecords['Equiv']['structuredContent']['sha'];put(case,p.name,raw)
p=base/'candidates/POSITIVE_APPLICATION.md';put(case,p.name,p.read_bytes());s['source_contract_sha256']=h(p.read_bytes());s['contract_reviewed']=True;files[case]=s
# Arithmetic forward: exact whitespace only, own evidence for both lanes.
case='arithmetic-forward';module='ScalarPolePreparation318';packet='forward-actual-two-descent-root-divisor-orders-r13'
b,a,s=source(case,packet,module,base/'candidates'/(module+'.lean'));assert a==b.replace('10<inputR','10 < inputR') and b.count('10<inputR')==1
s['evidence']=[];logs=[]
for lane,packet in [('descent',packet),('weighted','forward-original-weighted-weyl-r22-replay-r13')]:
 assert git(exp+packet+'/'+module+'.lean').decode()==b
 ep=base/(lane+'-logs/progress-experiments')/packet;s['evidence'].append(evidence(case,packet,base/(lane+'.zip'),ep,module));logs.append((ep/'logs'/(module+'.log')).read_text().replace(packet,'PACKET'))
assert logs[0]==logs[1]
for n in ['ScalarForwardWitness318','ScalarSmallPrimePreparation318','ScalarPackedLocalUnit318','AllScalarSupportPreparation318','PreparedLucasSource318','PreparedTwoThreeSource318','SmallPrimeFullSource318']:source_at(case,base/'candidates/primary'/(n+'.lean'))
p=base/'candidates/primary/Mathlib-Order-InitialSeg.lean';raw=p.read_bytes();assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==newrecords['InitialSeg']['structuredContent']['sha'];put(case,p.name,raw)
p=base/'candidates/FORWARD_APPLICATION.md';put(case,p.name,p.read_bytes());s['source_contract_sha256']=h(p.read_bytes());s['contract_reviewed']=True
for p in (base/'candidates/revision-snapshots').rglob('*'):
 if p.is_file():put(case,'revision-snapshots/'+str(p.relative_to(base/'candidates/revision-snapshots')),p.read_bytes())
files[case]=s
# Picard full dual algebra norm.
case='picard-five';base=root/'picard-run43586414080';packet='original-five-kernel-norm-equivalence-r17';module='OriginalDualAlgebraNormTrace318'
b,a,s=source(case,packet,module,base/'candidates/five'/(module+'.lean'))
expected=b.replace('  change Algebra.norm (DualNumber R) (equivalence R S (x ⊗ₜ[R] 1)) = _\n  rw [Algebra.norm_eq_of_algEquiv, OriginalRightTensorNormTrace318.norm_coefficient,','  have hx : equivalence R S (x ⊗ₜ[R] 1) = (inl x : DualNumber S) :=\n    DualNumberScalarExtension318.equivalence_left R S x\n  rw [← hx, Algebra.norm_eq_of_algEquiv (equivalence R S) (x ⊗ₜ[R] 1),\n    OriginalRightTensorNormTrace318.norm_coefficient,').replace('  rw [← hz, Algebra.norm_eq_of_algEquiv]','  rw [← hz, Algebra.norm_eq_of_algEquiv (equivalence R S) z.val]')
assert a==expected
s['evidence']=[evidence(case,packet,base/'evidence/five-r17.zip',base/'evidence/five-r17/progress-experiments'/packet,module)]
for n in ['OriginalRightTensorNormTrace318','ActualDualUnitNormIdentification318','OriginalFiniteFreeDualTransfer318']:snapshot_git(case,packet,n)
for n in ['DualNumberScalarExtension318','SquareZeroUnit318']:
 snapshot_git(case,packet,n)
put(case,'PINNED-NORM-EQUIVALENCE.json',(base/'primary/PINNED-NORM-EQUIVALENCE.json').read_bytes());s['contract_reviewed']=False;files[case]=s
(out/'NEXT-SOURCE-CHECK.json').write_text(json.dumps(files,indent=2)+'\n')
for k,v in files.items():print('PASS',k,v['before_sha256'],v['after_sha256'],len(v['evidence']),'own artifacts')
print('Exact source deltas/options/imports, own GitHub digests/ZIP/RESULT/intake and primary source identity checked; NO LEAN RUN')
