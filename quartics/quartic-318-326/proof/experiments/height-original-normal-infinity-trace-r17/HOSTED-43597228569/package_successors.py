from pathlib import Path
import json,hashlib,shutil,subprocess,sys,re
from machine_contracts import IDS,CONTRACTS
R=Path(__file__).resolve().parent;W=R.parent;C=R/'candidates';V=W/'review43597228569';REPO=W/'pel-integration43592150561/repo';EX=REPO/'quartics/quartic-318-326/proof/experiments';OUT=R/'successors';HEAD='2af419e128047c483b3cdc0ba5e4d65c09d7c4ce';h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();dump=lambda p,a:p.write_text(json.dumps(a,indent=2)+'\n')
def cp(s,d):
 d.parent.mkdir(parents=True,exist_ok=True)
 if d.exists():assert s.read_bytes()==d.read_bytes(),d
 else:shutil.copyfile(s,d)
sys.path.insert(0,str(REPO/'scripts'));import check_progress_experiment as pe,check_progress_lean as ci
plan=ci.derive_plan();sources=[json.loads((C/(n+'-MANIFEST.json')).read_text()) for n in ['SIGN','COERCIVITY','RESIDUE']];records={s['module']+'.lean':s for s in sources};assert len(records)==3
reviews=[V/'PEL-FIRST-TWO-SOURCE-BINDINGS.json',V/'PEL-RESIDUE-SOURCE-BINDINGS.json'];assert all(p.is_file() for p in reviews),'Wait for formal source reports'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()==HEAD
MAP={'zero':('pel-original-zero-local-length-r43','pel-original-zero-local-length-r44'),'cotangent':('pel-original-cotangent-hzero-forty-r49','pel-original-cotangent-hzero-forty-r50'),'torsion':('pel-original-torsion-towers-r23','pel-original-torsion-towers-r24'),'character':('pel-original-character-ordered-biholomorph-r16','pel-original-character-ordered-biholomorph-r17'),'trace':('height-original-normal-infinity-trace-r16','height-original-normal-infinity-trace-r17')}
OUT.mkdir(exist_ok=True);rows=[]
for lane,(old,new) in MAP.items():
 src=EX/old;dst=OUT/new;assert not dst.exists();dst.mkdir();d=json.loads((src/'intake.json').read_text());actual=[];copies={}
 for n,rec in d['files'].items():
  assert h(src/n)==rec['sha256'];cp(src/n,dst/n)
  if n in records:
   row=records[n];assert h(src/n)==row['before_sha256'];assert h(C/'after'/n)==row['after_sha256'];shutil.copyfile(C/'after'/n,dst/n);actual.append(n[:-5]);copies[n]=row
   assert re.findall(r'^.*set_option.*$',(src/n).read_text(),re.M)==re.findall(r'^.*set_option.*$',(dst/n).read_text(),re.M)
 actual=[n for n in d['order'] if n in actual];unchanged=[n for n in d['order'] if n not in actual]
 d.update(packet=new,status='DRAFT_SOURCE_REPAIR_HOSTED_PENDING',revision_of=old,revision_classification_schema=1,new_modules=[])
 for k in ['changed_modules','revised_modules','modified_predecessor_modules']:d[k]=actual
 for k in ['exact_predecessor_modules','unchanged_predecessor_modules','reused_modules']:
  if k in d:d[k]=unchanged
 if 'unchanged_producer_modules' in d:d['unchanged_producer_modules']=unchanged if isinstance(d['unchanged_producer_modules'],list) else len(unchanged)
 for n,row in d['files'].items():row['sha256']=h(dst/n)
 dump(dst/'intake.json',d);ev=dst/'HOSTED-43597228569';ev.mkdir();own=R/'logs'/(lane+'-artifact')/'progress-experiments'/old;assert json.loads((own/'RESULT.json').read_text())['packet_sha256']==h(src/'intake.json')
 shutil.copytree(own,ev/'own-hosted');shutil.copytree(C,ev/'canonical');shutil.copytree(R/'logs',ev/'logs');cp(src/'intake.json',ev/'PREDECESSOR-intake.json');cp(src/'APPLICATION.json',ev/'PREDECESSOR-APPLICATION.json');cp(src/'README.md',ev/'PREDECESSOR-README.md');cp(Path(__file__),ev/'package_successors.py');cp(R/'machine_contracts.py',ev/'machine_contracts.py')
 for bind in reviews:
  b=json.loads(bind.read_text());cp(bind,ev/'source-reviews'/bind.name);report=V/bind.name.replace('-BINDINGS.json','-REVIEW.md');assert report.is_file();cp(report,ev/'source-reviews'/report.name)
  for rel,digest in b['source_bindings'].items():assert h(V/rel)==digest,(bind.name,rel);cp(V/rel,ev/'source-reviews'/rel)
 caveat='Inherited IntegralOverlapRootGenerators318 has an earlier same-public-API proof body versus the geometry closure. It is unchanged, as is every trace geometry root in this successor. The retained earlier43588277165 center GlobalComparison full-module pass is not a trace pass; production CommonRestriction was tested and failed. Current trace stopped in PELPrimeLatticeResidues and did not reach geometry.'
 if lane=='trace':
  g=src/'HOSTED-43592150561/geometry-current-corroboration';assert g.is_dir();shutil.copytree(g,ev/'geometry-current-corroboration')
 dump(dst/'COPY-BINDINGS.json',{'predecessor':old,'successor':new,'copies':copies,'unchanged_count':len(unchanged),'full_order_count':len(d['order']),'own_hosted_result_sha256':h(own/'RESULT.json'),'own_predecessor_intake_sha256':h(src/'intake.json'),'trace_dependency_caveat':caveat if lane=='trace' else None,'geometry_sources_changed':False})
 text=f'# {new}\n\nSource-supported successor to {old}, own observed run43597228569 at2af419e128047c483b3cdc0ba5e4d65c09d7c4ce. Full {len(d["order"])}-module closure/order retained, {len(actual)} changed copies and {len(unchanged)} identical sources. Changed modules: '+', '.join(actual)+'.\n\nWhere propagated, NormalizedSignAction exposes the exact normalization projections before existing rewrites and splits finite product extensionality; all signed chart maps, both cases and eight infinity points remain. Its additional downstream/kernel diagnostics remain unresolved until actual hosted replay. Coercivity replaces only the failing scalar positivity tactic by alpha_pos, the existing hτ and positivity of20; all existing conditional public telescopes are unchanged. PrimeLatticeResidues only allows its existing simplifier to make no progress; final ring remains mandatory on every residual, with all four primes/two rows and symbolic residue vectors retained. No new public premise or target change occurs in this delta.\n\n'
 if lane=='trace':text+=caveat+' Exact older center/lattice evidence is retained as historical corroboration, not new geometry acceptance.\n\n'
 text+='All own artifact ZIPs/digests/results and exact published intakes, native source/consumer evidence, immutable source reviews and nine structured obligations are bound. No new preventive PEL edits, local Lean/Lake, resource/trust changes, admission, candidate kernel acceptance, full packet pass or complete arithmetic theorem claim. New packet-specific input/map/consumer propagation review and hosted replay remain required.\n';(dst/'README.md').write_text(text)
 obligations=[]
 for ix,key in enumerate(IDS):
  parts=[(n,CONTRACTS[n][0][ix]) for n in actual];refs=[];evidence=['README.md','HOSTED-43597228569/own-hosted/RESULT.json']
  for n in actual:
   refs += [n+'.lean','HOSTED-43597228569/canonical/before/'+n+'.lean'];evidence += ['HOSTED-43597228569/canonical/'+CONTRACTS[n][1],'HOSTED-43597228569/canonical/'+n+'.diff']
  for f in refs+evidence:assert (dst/f).is_file(),f
  obligations.append({'id':key,'required_input':' '.join(n+': '+t[0] for n,t in parts),'constructed_input':' '.join(n+': '+t[1] for n,t in parts),'justification':' '.join(n+': '+t[2] for n,t in parts),'scope_modules':actual,'source_references':refs,'evidence':evidence})
 a={'packet':new,'predecessor':old,'status':'DRAFT_SOURCE_REPAIR_HOSTED_PENDING','source_commit':HEAD,'integration_base_commit':HEAD,'observed_and_current_packet_tree_identical':True,'run_id':43597228569,'claim':'Observed PEL source-supported candidates only; no geometry source propagation this round.','local_lean_run':False,'kernel_verified':False,'independently_accepted':False,'full_arithmetic_theorem_proved':False,'resources_changed':False,'public_telescopes_changed':False,'public_telescope_disclosure':'All current public telescopes are unchanged. Existing Coercivity hτ assumptions remain explicit where propagated.','modified_predecessor_modules':actual,'new_modules':[],'obligations':obligations,'machine_contract_status':'DRAFT_REQUIRES_INDEPENDENT_PROPAGATION_REVIEW','intake_sha256':h(dst/'intake.json'),'copy_bindings_sha256':h(dst/'COPY-BINDINGS.json'),'sources':{n:h(dst/n) for n in d['files']}}
 if lane=='trace':a['trace_dependency_caveat']=caveat;a['geometry_sources_changed']=False
 a['bindings']={str(p.relative_to(dst)):h(p) for p in dst.rglob('*') if p.is_file() and p.parent!=dst};a['bindings'].update({'README.md':h(dst/'README.md'),'COPY-BINDINGS.json':h(dst/'COPY-BINDINGS.json')});dump(dst/'APPLICATION.json',a)
 prior=OUT/old;prior.mkdir(exist_ok=True)
 for n in ['intake.json',*d['files']]:cp(src/n,prior/n)
 pe.packet(new,plan,OUT);row={'predecessor':old,'successor':new,'lane':lane,'order_count':len(d['order']),'changed':actual,'intake_sha256':h(dst/'intake.json'),'application_sha256':h(dst/'APPLICATION.json')};rows.append(row);print('PASS',new,len(d['order']),len(actual),flush=True)
dump(R/'SUCCESSOR_MAP.json',{'base':HEAD,'observed_head':HEAD,'mapping':{a:b for a,b in MAP.values()},'packets':rows,'local_lean_executed':False});assert sum(len(r['changed']) for r in rows)==11
print('All5 source-supported drafts ready for independent45-obligation propagation review.')
