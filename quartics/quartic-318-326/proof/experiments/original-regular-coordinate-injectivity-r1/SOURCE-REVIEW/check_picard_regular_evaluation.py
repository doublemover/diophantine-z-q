from pathlib import Path
import hashlib,json,subprocess,re,shutil
B=Path('/workspace/scratch/41c6d5925c0e');O=B/'review43592150561';W=B/'picard-run43592150561/original-coordinate-algebra';R=B/'pel-integration43592150561/repo';H='2b151fc62f5872fd569489336d35f536d4cae0a4';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
c=json.loads((W/'CONTRACT.json').read_text());assert sha(W/'CONTRACT.json')=='e96b9c1189b1afd31280e8730dedefc16ca1373deac7bab290025e1250dd8d2e'
for n,h in c['bindings'].items():assert sha(W/n)==h,n
assert len(c['obligations'])==9
for ob in c['obligations'].values():
 for k in ['required_input','constructed_input','justification','source_references','evidence']:assert ob[k]
 for n in ob['source_references']+ob['evidence']:assert (W/n).is_file()
paths={};pre='quartics/quartic-318-326/proof/experiments/pel-original-character-ordered-biholomorph-r15/'
for p in (W/'source-snapshots').glob('*.lean'):
 assert subprocess.check_output(['git','show',H+':'+pre+p.name],cwd=R)==p.read_bytes(),p.name;paths[p.name]=pre+p.name
s=(W/'candidates/PELOriginalRegularCoordinateAlgebra318.lean').read_text();code=re.sub(r'/\-.*?\-/','',s,flags=re.S);assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|^set_option',code,re.M)
ss=O/'source-snapshots/picard-regular-evaluation';shutil.copytree(W,ss,dirs_exist_ok=True)
j={'status':'PASS_SOURCE_IDENTITIES_AND_CONTRACT','source_head':H,'candidate_sha256':sha(W/'candidates/PELOriginalRegularCoordinateAlgebra318.lean'),'contract_sha256':sha(W/'CONTRACT.json'),'published_sources':paths,'local_lean_run':False,'kernel_verified':False,'injectivity_not_in_this_module':True,'algebraization_claimed':False}
(O/'PICARD-REGULAR-EVALUATION-CHECK.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j,indent=2))
