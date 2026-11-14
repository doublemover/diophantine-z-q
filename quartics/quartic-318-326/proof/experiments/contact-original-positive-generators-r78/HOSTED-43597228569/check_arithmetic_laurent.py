from pathlib import Path
import hashlib,json,re,subprocess,shutil,zipfile
B=Path('/workspace/scratch/41c6d5925c0e');W=B/'arithmetic-run43597228569';C=W/'candidates';O=B/'review43597228569';R=B/'pel-integration43592150561/repo';H='2af419e128047c483b3cdc0ba5e4d65c09d7c4ce';X='quartics/quartic-318-326/proof/experiments/contact-original-positive-generators-r76/'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();M=json.loads((C/'POSITIVE_BINDINGS.json').read_text());assert M['head']==H and M['run']==43597228569
S=O/'source-snapshots/arithmetic-laurent';S.mkdir(parents=True,exist_ok=True)
def save(p,r):
 q=S/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
a=C/'ContactOriginalLaurentBoundary318.before.lean';b=C/'ContactOriginalLaurentBoundary318.lean';assert sha(a)==M['before_sha256'] and sha(b)==M['after_sha256'];assert sha(C/'POSITIVE_APPLICATION.md')==M['contract_sha256']
x=a.read_text();y=b.read_text();assert subprocess.check_output(['git','show',H+':'+X+b.name],cwd=R)==a.read_bytes()
assert re.findall(r'^set_option.*$',x,re.M)==re.findall(r'^set_option.*$',y,re.M)
for name in ['reindex_negative','negative_image','zero_iff','kernel_eq_boundary']:
 pat=r'lemma '+name+r'\b([\s\S]*?) := by';assert re.search(pat,x).group(1)==re.search(pat,y).group(1),name
assert x[x.index('lemma zero_iff'):x.index('/-- Exact geometric-to-Laurent')]==y[y.index('lemma zero_iff'):y.index('/-- Exact geometric-to-Laurent')]
assert re.findall(r'^public import.*$',y,re.M)==['public import all ContactOriginalCohomologyCoordinates318','public import all OriginalFiniteBasisBaseChange318','public import all ContactOriginalLaurentCoordinates318','public import all OriginalLineMayerVietorisQuotient318']
code=re.sub(r'/\-.*?\-/','',y,flags=re.S);assert not re.search(r'\b(sorry|axiom|admit|unsafe|implemented_by|native_decide)\b',code)
for p in [a,b,C/'POSITIVE_BINDINGS.json',C/'POSITIVE_APPLICATION.md',C/'ContactOriginalLaurentBoundary318.diff']:save(p,p.name)
for name,h in M['primary_sources'].items():
 p=C/'primary'/name;assert sha(p)==h;assert subprocess.check_output(['git','show',H+':'+X+name],cwd=R)==p.read_bytes();save(p,'primary/'+name)
art=json.loads((W/'positive-artifact.json').read_text());z=W/'positive.zip';assert art['id']==M['artifact_id'] and art['workflow_run']['head_sha']==H and art['workflow_run']['id']==43597228569 and art['digest']=='sha256:'+sha(z)
E=W/'positive-logs/progress-experiments/contact-original-positive-generators-r76';res=json.loads((E/'RESULT.json').read_text());assert res['commands'][-1]['module']==M['module'] and res['commands'][-1]['exit_code']==1
it=W/'positive-intake.before.json';assert sha(it)==M['intake_sha256']==res['packet_sha256'];assert subprocess.check_output(['git','show',H+':'+X+'intake.json'],cwd=R)==it.read_bytes()
with zipfile.ZipFile(z) as zz:
 assert zz.testzip() is None
 for n in zz.namelist():
  if not n.endswith('/'):assert zz.read(n)==(W/'positive-logs'/n).read_bytes()
for p in [W/'positive-artifact.json',E/'RESULT.json',E/'logs'/(M['module']+'.log'),it]:save(p,'evidence/'+p.name)
for n in ['Mathlib_LinearAlgebra_Span_Defs.lean','Mathlib_LinearAlgebra_Span_Defs.lean.provenance.json']:save(B/'review43592150561/research-native'/n,'native/'+n)
j={'status':'PASS_SOURCE_AND_CURRENT_HUMAN_CONTRACT_ONLY','after_sha256':M['after_sha256'],'contract_sha256':M['contract_sha256'],'run':M['run'],'head':H,'public_statements_unchanged':True,'import_all_support_explicit':True,'options_unchanged':True,'local_lean_run':False,'candidate_hosted_pass':False,'packet_propagation_review_complete':False,'source_bindings':{str(p.relative_to(O)):sha(p) for p in S.rglob('*') if p.is_file()}}
(O/'ARITHMETIC-LAURENT-SOURCE-CHECK.json').write_text(json.dumps(j,indent=2)+'\n');print('PASS one source,4 identical public statements,unchanged zero_iff body/options,12 exact primary copies,own artifact/intake/result; no Lean')
