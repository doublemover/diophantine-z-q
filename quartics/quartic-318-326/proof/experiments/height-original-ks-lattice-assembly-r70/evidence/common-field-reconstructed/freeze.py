from pathlib import Path
import subprocess,json,hashlib,re,shutil,sys
W=Path.cwd();R=W/'resume-20261115-repo';D=W/'geometry-common-field-reconstructed-20261117';T=W/'geometry-ks59-restored-integration'
base='f11df57cee8d78a54f1c8ac7134215ac0a31e995';prefix='quartics/quartic-318-326/proof/experiments/height-original-ks-lattice-assembly-r59';bp='quartics/quartic-318-326/proof/progress';name='OriginalIntegerCommonField318'
def git(*a):return subprocess.check_output(['git','-C',str(R),*a])
def H(b):return hashlib.sha256(b).hexdigest()
def J(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
intake=json.loads(git('show',base+':'+prefix+'/intake.json'));bm=json.loads(git('show',base+':'+bp+'/checkpoint-manifest.json'))
sys.path.insert(0,str(T/'scripts'));from check_progress_lean import import_names
sources={n:git('show',base+':'+prefix+'/'+n+'.lean') for n in intake['order']};sources[name]=(D/'sources'/f'{name}.lean').read_bytes()
B={n:git('show',base+':'+bp+'/'+n+'.lean') for n in bm['module_order']}
for n in intake['order']:assert H(sources[n])==intake['files'][n+'.lean']['sha256']
order=[];border=[];seen=set()
def walk(n):
 if n in seen:return
 seen.add(n)
 b=sources.get(n,B.get(n));assert b is not None,n
 for dep in sorted(import_names(b.decode())):
  if dep in sources or dep in B:walk(dep)
  else:assert dep.startswith(('Mathlib','Lean','Init','Batteries','Qq','Aesop')),dep
 (order if n in sources else border).append(n)
walk(name)
primary=['FourRootOrderLocalizationMaps318','OriginalIntegerReciprocalCharts318','OriginalIntegerReciprocalFractionField318','OriginalIntegerFractionField318','OriginalIntegerAffineModel318','OriginalIntegerNormalizationMap318','OriginalIntegerFiniteClosure318','OriginalIntegerNormalizedOverlap318','OriginalIntegerReciprocalNormalization318','IntegralClosureAwayField318','IntegralFourRootScalarMaps318','IntegralFourRootOverlap318','FourRootOrderOpenMaps318']
for n in primary:(D/'primary'/f'{n}.lean').write_bytes(sources[n])
for n in ['FractionFieldLocalizationDescent318','FourRootOrder318']:(D/'primary'/f'{n}.lean').write_bytes(B[n])
(D/'primary/intake.json').write_bytes(git('show',base+':'+prefix+'/intake.json'))
review=W/'resume-independent-review/ORDER40-HOSTED-44067548822-ASTRA-REVIEW.json';shutil.copyfile(review,D/'primary/KS59-HOSTED-REVIEW.json')
prior_review=prefix+'/evidence/N4A-RECIPROCAL-ORDER-NORMALIZATION-ASTRA-REVIEW.json'
(D/'primary/HISTORICAL-REVIEW-NOT-CURRENT-ACCEPTANCE.json').write_bytes(git('show',base+':'+prior_review))
(D/'README.md').write_text('''# Reconstructed common-order field embedding

The unpublished OriginalIntegerCommonField318 source formerly recorded as SHA23e57b7f was not found after the workspace rollback: a workspace-wide filename search, the current published Git tree, and the reviewer's restored workspace found no bytes. The historical three-source review survives, but is not acceptance of this reconstruction. This is freshly written source, not hash recovery or restoration of the lost file.

The candidate specializes the now strictly checked FourRootOrderLocalizationMaps318 to the actual finiteMap with the identity target equivalence, extends the already checked integer embedding by native Away.lift, proves injectivity from its exact restriction, and proves the same original fraction field. Laurent agreement is proved by native localization uniqueness on Z[X]. No new map is postulated, no twist/prime/root is inverted beyond the actual parameter, and no extra action coherence is assumed. The field scalar tower explicitly uses the named algebra projections. Normalization/finiteness/regularity/global claims are outside this file.

All 207 existing roots remain untouched. This one-source candidate requires fresh mathematical/source/API review and exact dependency rebase. No local Lean has run and no compiler acceptance is claimed. Any future packet must select this new source explicitly; the historical lost SHA is not the selected source.
''')
native_paths={'LocalizationDefs.lean':'Mathlib/RingTheory/Localization/Defs.lean','FractionRing.lean':'Mathlib/RingTheory/Localization/FractionRing.lean','AwayBasic.lean':'Mathlib/RingTheory/Localization/Away/Basic.lean','LocalizationLocalization.lean':'Mathlib/RingTheory/Localization/LocalizationLocalization.lean'}
J(D/'SOURCE-APPLICATION.json',dict(status='NEW_RECONSTRUCTION_REQUIRES_FRESH_REVIEW_NOT_LEAN',lost_original_sha256='23e57b7ff9a5a29408d2e864cd7cefe38a49fb55a630b31480fbc375b6b4fbe9',source_sha256=H(sources[name]),base_commit=base,predecessor_subtree=git('rev-parse',base+':'+prefix).decode().strip(),bindings={p.relative_to(D).as_posix():H(p.read_bytes()) for folder in ['sources','primary','native'] for p in sorted((D/folder).rglob('*')) if p.is_file()},native={n:dict(path=p,pin='56a005855ea17e0b0958f73ec801ae140b0a1679',sha256=H((D/'native'/n).read_bytes()),git_blob=git('hash-object',str(D/'native'/n)).decode().strip()) for n,p in native_paths.items()},claims=['actual finite localization and injectivity','actual common-order embedding into original field','actual common fraction field','equality of Laurent restriction with existing finite Laurent field action'],excludes=['reciprocal order normalization','finite normalization','regularity','global model or KS'],local_lean_run=False))
J(D/'DEPENDENCY-REBASE.json',dict(base_commit=base,predecessor=prefix,source_application_sha256=H((D/'SOURCE-APPLICATION.json').read_bytes()),new_modules=[name],predecessor_roots=207,unchanged_predecessor_sources={n:H(sources[n]) for n in intake['order']},target=name,target_order=order,baseline_order=border,target_count=len(order),baseline_count=len(border),target_hashes={n:H(sources[n]) for n in order},baseline_hashes={n:H(B[n]) for n in border},KS59_checked_sources=json.loads(review.read_text())['selected_source_hashes'],local_lean_run=False))
print(json.dumps({'source_sha':H(sources[name]),'source_manifest':H((D/'SOURCE-APPLICATION.json').read_bytes()),'rebase':H((D/'DEPENDENCY-REBASE.json').read_bytes()),'closure':len(order),'baseline':len(border),'native':json.loads((D/'SOURCE-APPLICATION.json').read_text())['native']},indent=2))
