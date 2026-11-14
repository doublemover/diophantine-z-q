from pathlib import Path
import json,hashlib,subprocess,re,zipfile
D=Path('/workspace/scratch/41c6d5925c0e/review43586414080')
exec((D/'check_next_sources.py').read_text().split('# Arithmetic positive.')[0])
base=root/'pel-run43586414080';m=json.loads((base/'candidates/CANONICAL-MANIFEST.json').read_text());native=json.loads((out/'PEL-OTHER-INDEPENDENT-PRIMARY.json').read_text());results=[]
assert h((base/'candidates/OTHER-APPLICATION.md').read_bytes())=='9a7fac63c1cfc3a17e7cb024be6785ccbd5b022c2b1a8931de4c2f963a4691b9'
for row in m['sources'][1:]:
 module=row['module'].removesuffix('.lean');case='pel-other/'+module;packet=row['own_evidence'][0]['predecessor']
 b,a,s=source(case,packet,module,base/'candidates/after'/row['module']);assert h(b.encode())==row['before_sha256'] and h(a.encode())==row['after_sha256'];assert (base/'candidates/before'/row['module']).read_text()==b
 if module=='PELOriginalSiegelNormalization318':
  assert b.split('lemma denormalize_normalize')[0]==a.split('lemma denormalize_normalize')[0]
  assert b.split('@[expose] def normalization')[1]==a.split('@[expose] def normalization')[1]
  for name in ['denormalize_normalize','normalize_denormalize']:
   assert b.split('lemma '+name)[1].split(':=by')[0]==a.split('lemma '+name)[1].split(':=by')[0]
 else:
  expected=b.replace('  have hh := congrArg quotientEquiv h\n  simpa only [quotientEquiv_mk,parity_word] using hh','  have hh := congrArg (fun q:QuotientNormalizer => Multiplicative.toAdd (quotientEquiv q)) h\n  simpa only [quotientEquiv_mk,parity_word,toAdd_ofAdd] using hh').replace('  rw [quotientEquiv_mk,parity_word]\n','  rw [quotientEquiv_mk,parity_word,ofAdd_toAdd]\n').replace('  intro i j h\n  rw [inertia_class','  intro i j h\n  change (QuotientGroup.mk (inertiaElement i):QuotientNormalizer)=\n    QuotientGroup.mk (inertiaElement j) at h\n  rw [inertia_class')
  assert a==expected
 s['evidence']=[]
 for ev in row['own_evidence']:
  pkt=ev['predecessor'];lane=ev['lane'];assert git(exp+pkt+'/'+module+'.lean').decode()==b
  assert subprocess.check_output(['git','show',m['current_integration_head']+':'+exp+pkt+'/'+module+'.lean'],cwd=root/'geometry-integration43583139321/repo').decode()==b
  ep=base/'logs'/(lane+'-artifact')/'progress-experiments'/pkt
  ss=evidence(case,pkt,base/'logs'/(lane+'-artifact.zip'),ep,module);assert ss['log_sha256']==ev['log_sha256'];assert ss['result_sha256']==ev['result_sha256'];assert ss['intake_sha256']==ev['predecessor_intake_sha256'];s['evidence'].append(ss)
 for n in (['PELOriginalGaugedTheta318','PELOriginalThetaHermitianGauge318'] if 'Siegel' in module else ['PELPositiveOrderNormalizer318','PELPrimeRightLattice318']):snapshot_git(case,packet,n)
 put(case,'OTHER-APPLICATION.md',(base/'candidates/OTHER-APPLICATION.md').read_bytes());s['human_contract_reviewed']=True;results.append(s)
for key,fn in [('Units','Mathlib_Algebra_GroupWithZero_Units_Basic.lean'),('Tags','Mathlib_Algebra_Group_TypeTags_Basic.lean')]:
 p=base/'candidates/primary'/fn;raw=p.read_bytes();assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==native[key]['structuredContent']['sha'];put('pel-other/primary',fn,raw)
put('pel-other','CANONICAL-MANIFEST.json',(base/'candidates/CANONICAL-MANIFEST.json').read_bytes())
scan=json.loads((base/'candidates/consumer-evidence/PARITY-CONSUMER-SCAN.json').read_text())
for pkt,row in scan.items():
 intake=json.loads(git(exp+pkt+'/intake.json'));assert len(intake['order'])==row['root_file_count'];found=[]
 for n in intake['order']:
  if n=='PELNormalizerParityQuotient318':continue
  txt=git(exp+pkt+'/'+n+'.lean').decode()
  for ln,line in enumerate(txt.splitlines(),1):
   if line.startswith('public import '):continue
   if any(term in line for term in row['search_terms']):found.append((n,ln,line))
 assert not found,found
put('pel-other','PARITY-CONSUMER-SCAN.json',(base/'candidates/consumer-evidence/PARITY-CONSUMER-SCAN.json').read_bytes())
(out/'PEL-OTHER-SOURCE-CHECK.json').write_text(json.dumps(results,indent=2)+'\n')
print('PASS both exact candidates/imports/options/public headers; three own GitHub artifacts/ZIPs/RESULTs/intakes; pinned API blobs; original consumers and negative qualified quotient scan. NO LEAN RUN.')
