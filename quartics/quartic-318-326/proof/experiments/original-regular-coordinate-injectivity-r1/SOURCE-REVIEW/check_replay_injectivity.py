from pathlib import Path
import hashlib,json,shutil,re,itertools
B=Path('/workspace/scratch/41c6d5925c0e');W=B/'replay-original-injectivity';O=B/'review43592150561';S=O/'source-snapshots/replay-injectivity';S.mkdir(parents=True,exist_ok=True);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
M=json.loads((W/'CONTRACT.json').read_text());ev=B/'picard-run43592150561/original-coordinate-algebra/candidates/PELOriginalRegularCoordinateAlgebra318.lean';assert sha(ev)==M['input_evaluation_sha256']
def save(p,r):
 q=S/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
for n,h in M['sources'].items():
 p=W/'candidates'/n;assert sha(p)==h;save(p,'candidates/'+n);t=re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S);t=re.sub(r'--[^\n]*','',t)
 assert not re.search(r'\b(sorry|axiom|admit|unsafe|native_decide|implemented_by)\b|set_option',t)
assert 'decide +kernel' in (W/'candidates/FourRootSignCoefficientExtraction318.lean').read_text()
sp=(W/'candidates/FourRootCoordinateMonomialSpanning318.lean').read_text();assert 'Function.update_same' not in sp and 'Function.update_self' in sp
for text in ['public import Mathlib.LinearAlgebra.Finsupp.LinearCombination','(Submodule.mem_span_range_iff_exists_fun P).mp','Polynomial.aeval_X','Polynomial.aeval_C','Ideal.Quotient.inductionOn','MvPolynomial.induction_on','Submodule.span_induction']:assert text in sp
for p in (O/'research-native').iterdir():
 if p.suffix=='.json':
  j=json.loads(p.read_text()); data=(O/'research-native'/p.name.removesuffix('.provenance.json')).read_bytes()
  # Reviewer-fetched exact primary sources have pinned full-ref URLs and Git blob identities.
  assert '56a005855ea17e0b0958f73ec801ae140b0a1679' in str(j)
  assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==j['sha']
for p in [W/'CONTRACT.json',W/'README.md']:save(p,p.name)
for p in (W/'review-snapshots').rglob('*'):
 if p.is_file():save(p,p.relative_to(W))
save(ev,'input/PELOriginalRegularCoordinateAlgebra318.lean')
for p in (O/'research-native').iterdir():
 if p.is_file():save(p,'native/'+p.name)
# Exact finite rational character certificate independently enumerated in Python; this is not Lean execution.
masks=list(itertools.product([False,True],repeat=4));weight=lambda m,s:(-1)**sum(a and b for a,b in zip(m,s))
for m in masks:
 for n in masks:assert sum(weight(m,s)*weight(n,s) for s in masks)==(16 if m==n else 0)
j={'status':'PASS_CONNECTED_SOURCE_DESIGN_ONLY','sources':M['sources'],'input_evaluation_sha256':sha(ev),'contract_sha256':sha(W/'CONTRACT.json'),'orthogonality_pairs_checked':256,'minimal_contract_only':True,'nine_obligation_contract_review_complete':False,'local_lean_run':False,'kernel_verified':False,'global_algebraization_proved':False,'source_bindings':{str(p.relative_to(O)):sha(p) for p in S.rglob('*') if p.is_file()}}
(O/'REPLAY-INJECTIVITY-SOURCE-CHECK.json').write_text(json.dumps(j,indent=2)+'\n');print('PASS: exact4 sources, all correction snapshots, native primary evidence,16-mask/256-pair rational orthogonality; no Lean.')
