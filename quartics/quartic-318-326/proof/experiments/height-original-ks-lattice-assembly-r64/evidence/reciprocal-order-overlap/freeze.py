from pathlib import Path
import subprocess,json,hashlib,sys,shutil
W=Path.cwd();R=W/'resume-20261115-repo';D=W/'geometry-reciprocal-order-overlap-20261117';T=W/'geometry-ks60-reconstructed-integration';base='62feedd2112a14c8ba791d3d92c3df2c0375d180';prefix='quartics/quartic-318-326/proof/experiments/height-original-ks-lattice-assembly-r60';bp='quartics/quartic-318-326/proof/progress';name='OriginalIntegerReciprocalOrderOverlap318'
def g(p):return subprocess.check_output(['git','-C',str(R),'show',base+':'+p])
H=lambda b:hashlib.sha256(b).hexdigest()
def J(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
i=json.loads(g(prefix+'/intake.json'));b=json.loads(g(bp+'/checkpoint-manifest.json'));S={n:g(prefix+'/'+n+'.lean') for n in i['order']};S[name]=(D/'sources'/(name+'.lean')).read_bytes();B={n:g(bp+'/'+n+'.lean') for n in b['module_order']}
sys.path.insert(0,str(T/'scripts'));from check_progress_lean import import_names
seen=set();order=[];bo=[]
def walk(n):
 if n in seen:return
 seen.add(n);raw=S.get(n,B.get(n));assert raw is not None,n
 for dep in sorted(import_names(raw.decode())):
  if dep in S or dep in B:walk(dep)
  else:assert dep.startswith(('Mathlib','Lean','Init','Batteries','Qq','Aesop')),dep
 (order if n in S else bo).append(n)
walk(name)
assert 'OriginalIntegerCommonField318' not in order
primary=['FourRootOrderLocalizationMaps318','FourRootOrderOpenMaps318','OriginalIntegerReciprocalCharts318','OriginalIntegerAffineModel318','IntegralFourRootScalarMaps318','IntegralFourRootOverlap318','IntegralFourRootReciprocalCharts318','IntegralWholeReciprocalLocalization318']
for n in primary:(D/'primary'/(n+'.lean')).write_bytes(S[n])
(D/'primary/FourRootOrder318.lean').write_bytes(B['FourRootOrder318'])
inv=json.loads((W/'hosted-monitor-44073600873/common57/INVENTORY.json').read_text());passed={n:r['source_sha256']for n,r in inv['modules'].items()if r['status']=='compile_pass'};deps=[n for n in order if n!=name];assert all(n in passed and H(S[n])==passed[n]for n in deps)
shutil.copyfile(W/'resume-independent-review/COMMON57-HOSTED-44073600873-ASTRA-REVIEW.json',D/'primary/COMMON57-PARTIAL-HOSTED-REVIEW.json')
(D/'README.md').write_text('''# Independent reciprocal-order overlap bridge

New source, not restoration of the lost reciprocal-order normalization source. It specializes the strictly checked generic localization helper to the actual reciprocal four-root coefficients and the existing fullOverlap equivalence. The reciprocal polynomial-to-Laurent action is selected explicitly after fixing the common order and its Laurent action. map_identity pins the exact previous infinityMap. Localization/injectivity and the exact coefficient square use no common-field theorem, domain assumption on the order, finite-closure premise or regularity assumption.

This source does NOT import OriginalIntegerCommonField318: it is genuinely independent of the currently failed/pending KS60/61 target. All imported draft sources match strict passes in the authenticated56-module subset, but this new specialization has not been compiled. Actual dictionary conversion and performance remain hosted obligations. No fraction-field, order normalization, finiteness, properness or regularity conclusion is included. No publication is requested by this standalone package.
''')
app={'status':'NEW_INDEPENDENT_SOURCE_REQUIRES_REVIEW_NOT_LEAN','base_commit':base,'source_sha256':H(S[name]),'bindings':{p.relative_to(D).as_posix():H(p.read_bytes())for folder in ['sources','primary']for p in sorted((D/folder).rglob('*'))if p.is_file()},'claims':['exact existing reciprocal map identity','actual parameter localization under that map','injectivity without assuming order domain','literal reciprocal polynomial square'],'not_imported':'OriginalIntegerCommonField318','no_extra_hypotheses':True,'local_lean_run':False,'whole_goal_proved':False};J(D/'SOURCE-APPLICATION.json',app)
J(D/'DEPENDENCY-REBASE.json',{'base_commit':base,'predecessor_packet':prefix,'source_application_sha256':H((D/'SOURCE-APPLICATION.json').read_bytes()),'new_modules':[name],'target_order':order,'baseline_order':bo,'target_count':len(order),'baseline_count':len(bo),'target_hashes':{n:H(S[n])for n in order},'baseline_hashes':{n:H(B[n])for n in bo},'checked_imported_draft_sources':{n:passed[n]for n in deps},'pending_common_field_dependency':False,'publication_requested':False})
print(json.dumps({'source':H(S[name]),'application':H((D/'SOURCE-APPLICATION.json').read_bytes()),'rebase':H((D/'DEPENDENCY-REBASE.json').read_bytes()),'target_count':len(order),'baseline':len(bo),'checked_predecessors':len(deps)},indent=2))
