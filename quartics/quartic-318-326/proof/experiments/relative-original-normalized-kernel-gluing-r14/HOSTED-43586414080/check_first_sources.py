import pathlib, json, hashlib, subprocess, zipfile, re, shutil
root=pathlib.Path('/workspace/scratch/41c6d5925c0e'); out=root/'review43586414080'; repo=root/'pel-integration43582938856/repo'; head='f89bd0a3cb8a788d6c7f2f494a21d7d103a893cb'; exp='quartics/quartic-318-326/proof/experiments/'
h=lambda b:hashlib.sha256(b).hexdigest()
records=json.loads((out/'INDEPENDENT-GITHUB-PRIMARY-RECORDS.json').read_text()); arts=records['artifacts']['structuredContent']['artifacts']
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
# Sphere: exactly two intended codomain annotations.
case='sphere';base=root/'pel-run43586414080';module='ComplexSphereAffineNormalization318';packet='pel-original-zero-local-length-r41'
b,a,s=source(case,packet,module,base/'candidates/after'/(module+'.lean'))
assert a==b.replace('poleCoordinate p p=∞','poleCoordinate p p=(∞:OnePoint ℂ)').replace('inversion ((1*z+-z:ℂ):OnePoint ℂ)=∞','inversion ((1*z+-z:ℂ):OnePoint ℂ)=(∞:OnePoint ℂ)')
# Exact actual spacing of second replacement is checked via patch/count below if this assertion changes.
e=[]
for lane,p in [('zero',packet),('cotangent','pel-original-cotangent-hzero-forty-r47')]:
 assert git(exp+p+'/'+module+'.lean').decode()==b
 e.append(evidence(case,p,base/'logs'/f'{lane}-artifact.zip',base/'logs'/f'{lane}-artifact/progress-experiments'/p,module))
for n in ['SPHERE-APPLICATION.md','SPHERE-MANIFEST.json']:put(case,n,(base/'candidates'/n).read_bytes())
for n in ['ComplexSphereFourPointNormalization318','ProjectiveLineFourPointAlgebraicNormalization318','SphereInversion318','ComplexSphereAffineAutomorphisms318']:snapshot_git(case,packet,n)
primary=base/'candidates/primary/Mathlib_Topology_Compactification_OnePoint_Basic.lean';raw=primary.read_bytes();assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==records['OnePoint']['structuredContent']['sha'];put(case,primary.name,raw)
s.update(evidence=e,source_contract_sha256=h((base/'candidates/SPHERE-APPLICATION.md').read_bytes()),contract_reviewed=True);files[case]=s
# Picard finite exact cover construction.
case='finite';base=root/'picard-run43586414080';packet='original-finite-quotient-reconstruction-r69';module='OriginalFiniteProjectiveFlat318'
b,a,s=source(case,packet,module,base/'candidates/finite'/(module+'.lean'))
producer=git(exp+packet+'/OriginalProjectiveBaseIntegral318.lean').decode();block=producer[producer.index('  let C :'):producer.index('  letI : ∀ i : C.I₀')]
assert a==b.replace('  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat) (JLineAtlas318.cover ℚ)]',block+'  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat) C]')
s['evidence']=[evidence(case,packet,base/'evidence/finite-r69.zip',base/'evidence/finite-r69/progress-experiments'/packet,module)]
for n in ['OriginalProjectiveBaseIntegral318','OriginalFinitePointReconstruction318','OriginalFiberPointReconstruction318']:snapshot_git(case,packet,n)
put(case,'JLineAtlas318.lean',git('quartics/quartic-318-326/proof/progress/JLineAtlas318.lean'));put(case,'SOURCE.diff',(base/'candidates/finite/SOURCE.diff').read_bytes());s['contract_reviewed']=False;files[case]=s
# Gluing three normalization locations only.
case='gluing';packet='relative-original-normalized-kernel-gluing-r13';module='OriginalPullbackSquarePasting318'
b,a,s=source(case,packet,module,base/'candidates/gluing'/(module+'.lean'))
expected=b.replace('Scheme.Modules.pullbackCongr,eqToIso_refl,NatTrans.id_app','Scheme.Modules.pullbackCongr,eqToIso_refl,Iso.refl_hom,NatTrans.id_app').replace('        Functor.map_id,Category.id_comp]','        CategoryTheory.Functor.map_id,Category.id_comp]').replace('A1,B0,A3,A4,A6,A8,Scheme.Modules.pullbackCongr,eqToIso_refl,','A1,B0,A3,A4,A6,A8,Scheme.Modules.pullbackCongr,eqToIso_refl,Iso.refl_hom,Iso.app_inv,')
assert a==expected
s['evidence']=[evidence(case,packet,base/'evidence/gluing-r13.zip',base/'evidence/gluing-r13/progress-experiments'/packet,module)]
for n in ['OriginalLineSquareSections318','ContactCoefficientRestrictionSquares318']:snapshot_git(case,packet,n)
# Producer is baseline, not packet shadow.
put(case,'PullbackPathComposition318.lean',git('quartics/quartic-318-326/proof/progress/PullbackPathComposition318.lean'))
put(case,'SOURCE.diff',(base/'candidates/gluing/SOURCE.diff').read_bytes());put(case,'PINNED-PASTING-NORMALIZATION.json',(base/'primary/PINNED-PASTING-NORMALIZATION.json').read_bytes());s['contract_reviewed']=False;files[case]=s
(out/'FIRST-SOURCE-CHECK.json').write_text(json.dumps(files,indent=2)+'\n')
for k,v in files.items():print('PASS',k,v['before_sha256'],v['after_sha256'],len(v['evidence']),'own artifacts')
print('Source-only exact deltas, Git provenance, own ZIP/log/RESULT/intake, preserved options/imports checked; NO LEAN RUN')
