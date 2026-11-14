from pathlib import Path
import hashlib,json,subprocess,re,difflib,shutil
W=Path('/workspace/scratch/41c6d5925c0e'); D=W/'review43586414080'; R=W/'pel-integration43582938856/repo'; H='f89bd0a3cb8a788d6c7f2f494a21d7d103a893cb'; E='quartics/quartic-318-326/proof/experiments/'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(path):return subprocess.check_output(['git','-C',str(R),'show',H+':'+path])
def save(folder,name,b):
 p=D/'preventive-snapshots'/folder/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return p
pmap={'OriginalFinitePointReconstruction318':'original-finite-quotient-reconstruction-r69','OriginalSectionPullbackComposition318':'relative-original-normalized-kernel-gluing-r13','OriginalLineSquareSections318':'relative-original-normalized-kernel-gluing-r13','ContactCoefficientRestrictionSquares318':'relative-original-normalized-kernel-gluing-r13'}
rows=[]
for n,pkt in pmap.items():
 b=git(E+pkt+'/'+n+'.lean');a=(W/'picard-run43586414080/candidates/forward'/f'{n}.lean').read_bytes();s=b.decode();t=a.decode()
 assert re.findall(r'^.*(?:import|set_option).*$',s,re.M)==re.findall(r'^.*(?:import|set_option).*$',t,re.M)
 if n=='OriginalFinitePointReconstruction318':
  expected=s.replace('local instance baseIntegral : IsIntegral (ProjectiveJLine318.scheme ℚ) :=\n  OriginalProjectiveBaseIntegral318.integral p\n','').replace('local instance actualBase : Algebra (RatFunc ℚ) Y.functionField :=\n  OriginalSchemeDeckFieldAction318.baseAlgebra p OriginalProjectiveFunctionCoordinate318.κ\n','').replace('    (OriginalGenericStalkNaturality318.generic Y ≫ p =','    letI := OriginalQuotientRankFixed318.baseIntegral p\n    letI := OriginalQuotientRankFixed318.actualBase p\n    (OriginalGenericStalkNaturality318.generic Y ≫ p =').replace('  exact OriginalFiberPointReconstruction318.original_curve','  letI := OriginalQuotientRankFixed318.baseIntegral p\n  letI := OriginalQuotientRankFixed318.actualBase p\n  exact OriginalFiberPointReconstruction318.original_curve')
  assert t==expected
 else:
  added={'OriginalSectionPullbackComposition318':['Iso.refl_hom'],'OriginalLineSquareSections318':['Iso.trans_inv','Iso.refl_hom','Iso.refl_inv','Iso.app_hom','Iso.app_inv'],'ContactCoefficientRestrictionSquares318':['Iso.trans_inv','Iso.refl_hom','Iso.refl_inv']}[n]
  # Removing precisely the inserted normalization tokens reconstructs the predecessor modulo whitespace.
  u=t
  for tok in added:
   expected_count=s.count(tok)+(2 if n.startswith('Contact') else 1);assert t.count(tok)==expected_count,(n,tok)
  # Every non-equal line block differs solely by the specified lemma tokens and whitespace.
  for tag,i,j,k,l in difflib.SequenceMatcher(None,s.splitlines(True),t.splitlines(True)).get_opcodes():
   if tag=='equal':continue
   old=''.join(s.splitlines(True)[i:j]);new=''.join(t.splitlines(True)[k:l])
   for tok in added:new=new.replace(tok+',','')
   assert re.sub(r'\s','',old)==re.sub(r'\s','',new),(n,old,new)
 save('picard/'+n,'before.lean',b);save('picard/'+n,'after.lean',a)
 save('picard/'+n,'SOURCE.diff',''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True))).encode())
 rows.append(dict(module=n,packet=pkt,before_sha256=sha(b),after_sha256=sha(a),hosted_failure_observed=False))
for n in ['OriginalFiberPointReconstruction318','OriginalQuotientRankFixed318','OriginalFiniteProjectiveFlat318','OriginalProjectiveBaseIntegral318']:
 save('picard/primary',n+'.lean',git(E+pmap['OriginalFinitePointReconstruction318']+'/'+n+'.lean'))
for n in ['OriginalPullbackSquarePasting318','ContactCoefficientLineCharts318','ContactCoefficientSectionEquivalences318','ContactRelativeCoefficientChange318','ContactOriginalRelativeLineOverlap318']:
 save('picard/primary',n+'.lean',git(E+pmap['OriginalLineSquareSections318']+'/'+n+'.lean'))
# Exact current reviewed upstream flat source is context, not a new observed pass.
save('picard/primary','Candidate-OriginalFiniteProjectiveFlat318.lean',(W/'picard-run43586414080/candidates/finite/OriginalFiniteProjectiveFlat318.lean').read_bytes())
(D/'PICARD-PREVENTIVE-CHECK.json').write_text(json.dumps(dict(status='PASS',review_kind='PREVENTIVE_UNOBSERVED_SOURCE_ONLY',head=H,candidates=rows,local_lean_run=False,kernel_verified=False),indent=2)+'\n')
print('PICARD four exact candidate deltas PASS')
A=W/'arithmetic-lexical-preflight43586414080';m=json.loads((A/'MANIFEST.json').read_text()); assert sha((A/'MANIFEST.json').read_bytes())=='c33e42f2d4ecf458b83bb3d67c907dccb0fd43dc4db2774b890a4ee5a07245fb'
for k,f in [('application_sha256','APPLICATION.md'),('patch_sha256','PREVENTATIVE-SOURCE-ONLY.patch'),('script_sha256','prepare.py')]:assert sha((A/f).read_bytes())==m[k]
for f,h in m['supporting_trigger_evidence'].items():assert sha((A/f).read_bytes())==h
pkts=['forward-actual-two-descent-root-divisor-orders-r13','forward-original-weighted-weyl-r22-replay-r13'];pat=re.compile(r'(<|≤)(?=i[A-Za-z_])');total=0;patch=[]
for row in m['candidates']:
 n=row['module'];b=(A/'candidates'/n/'before.lean').read_bytes();a=(A/'candidates'/n/'after.lean').read_bytes();s=b.decode();t=a.decode()
 assert sha(b)==row['before_sha256'] and sha(a)==row['after_sha256'];assert not row['hosted_failure_observed'];assert n!='ScalarPolePreparation318'
 expected,count=pat.subn(lambda x:x[1]+' ',s);assert t==expected and count==row['inserted_spaces'];assert len(a)-len(b)==count;assert re.sub(r'\s','',s)==re.sub(r'\s','',t);total+=count
 for pkt in pkts:
  rel=E+pkt+'/'+n+'.lean';assert git(rel)==b
  patch.extend(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
 for f in (A/'candidates'/n).iterdir():save('arithmetic/'+n,f.name,f.read_bytes())
assert total==17 and len(m['candidates'])==9 and ''.join(patch).encode()==(A/'PREVENTATIVE-SOURCE-ONLY.patch').read_bytes()
# Independently repeat read-only lexical coverage over exact three predecessor closures.
unique=set();hits=[]
for pkt in ['contact-original-positive-generators-r74']+pkts:
 intake=json.loads(git(E+pkt+'/intake.json'))
 for order,n in enumerate(intake['order']):
  b=git(E+pkt+'/'+n+'.lean');unique.add((n,sha(b)))
  for ln,line in enumerate(b.decode().splitlines(),1):
   ms=list(pat.finditer(line))
   if ms:hits.append(dict(packet=pkt,module=n,order_index=order,line=ln,occurrences=len(ms),text=line.strip(),source_sha256=sha(b)))
assert len(unique)==1539 and hits==m['all_occurrences']
for f in ['MANIFEST.json','MANIFEST.before-trigger-evidence.json','APPLICATION.md','PREVENTATIVE-SOURCE-ONLY.patch','prepare.py']:
 save('arithmetic',f,(A/f).read_bytes())
for parent in ['primary','evidence']:
 for p in (A/parent).rglob('*'):
  if p.is_file():save('arithmetic',p.relative_to(A).as_posix(),p.read_bytes())
primary=(A/'primary/Mathlib-Order-InitialSeg.lean').read_bytes();assert hashlib.sha1(b'blob '+str(len(primary)).encode()+b'\0'+primary).hexdigest()=='568fc55fafade73ee81825d91ecfa9afd526362c'
assert '" <i "' in primary.decode() and '" ≤i "' in primary.decode()
(D/'ARITHMETIC-PREVENTIVE-CHECK.json').write_text(json.dumps(dict(status='PASS',head=H,review_kind='PREVENTIVE_UNOBSERVED_SOURCE_ONLY',candidates=m['candidates'],copies=18,inserted_spaces_per_closure=17,unique_scan_pairs=1539,source_manifest_sha256=sha((A/'MANIFEST.json').read_bytes()),local_lean_run=False,kernel_verified=False),indent=2)+'\n')
print('ARITHMETIC nine exact candidate deltas, 18 Git copies, 17 spaces per closure, full 1539-pair scan PASS')
