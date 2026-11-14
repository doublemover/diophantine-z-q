from pathlib import Path
import json,hashlib,shutil,sys,re,subprocess
from machine_contracts import CONTRACTS,IDS
W=Path(__file__).resolve().parent.parent;R=Path(__file__).resolve().parent;C=R/'candidates';REPO=W/'geometry-integration43583139321/repo';EX=REPO/'quartics/quartic-318-326/proof/experiments';OUT=R/'successors';V=W/'review43586414080';G=W/'geometry-run43583139321';GPK=G/'successors/height-original-ks-lattice-assembly-r16';GE=W/'geometry-run43588277165/evidence'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def cp(src,dst):
 dst.parent.mkdir(parents=True,exist_ok=True)
 if dst.exists():assert dst.read_bytes()==src.read_bytes(),dst
 else:shutil.copyfile(src,dst)
sys.path.insert(0,str(REPO/'scripts'));import check_progress_experiment as pe,check_progress_lean as ci
plan=ci.derive_plan();manifest=json.loads((C/'CANONICAL-MANIFEST.json').read_text());records={s['module']:s for s in manifest['sources']}
reviews=list(V.glob('PEL-*-SOURCE-BINDINGS.json'));assert len(reviews)>=2,'Await final three-source reports'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()==manifest['current_integration_head']
MAP={'zero':('pel-original-zero-local-length-r41','pel-original-zero-local-length-r42'),'cotangent':('pel-original-cotangent-hzero-forty-r47','pel-original-cotangent-hzero-forty-r48'),'torsion':('pel-original-torsion-towers-r21','pel-original-torsion-towers-r22'),'character':('pel-original-character-ordered-biholomorph-r14','pel-original-character-ordered-biholomorph-r15'),'trace':('height-original-normal-infinity-trace-r14','height-original-normal-infinity-trace-r15')}
GEOM=['IntegralRationalGlobalComparison318.lean','IntegralOriginalCommonRestriction318.lean']
for n in GEOM:
 records[n]={'module':n,'before_sha256':h(G/'candidates'/(n+'.before')),'after_sha256':h(G/'candidates'/n),'canonical_path':str(G/'candidates'/n),'geometry_propagation':True,'own_observed_run':43583139321,'published_commit':manifest['current_integration_head'],'current_common_full_module_failure':n==GEOM[1]}
OUT.mkdir(exist_ok=True);rows=[]
for lane,(old,new) in MAP.items():
 src=EX/old;dst=OUT/new;assert not dst.exists(),dst;dst.mkdir();data=json.loads((src/'intake.json').read_text());actual=[];copies={}
 for n in data['files']:
  assert h(src/n)==data['files'][n]['sha256'];cp(src/n,dst/n)
  if n in records:
   row=records[n];assert h(src/n)==row['before_sha256'],(old,n,'before mismatch');candidate=Path(row['canonical_path']) if row.get('geometry_propagation') else C/'after'/n
   shutil.copyfile(candidate,dst/n);assert h(dst/n)==row['after_sha256'];actual.append(n[:-5]);copies[n]=dict(row,canonical_path=str(candidate))
   assert re.findall(r'^.*set_option.*$',(src/n).read_text(),re.M)==re.findall(r'^.*set_option.*$',(dst/n).read_text(),re.M)
 actual=[n for n in data['order'] if n in actual];unchanged=[n for n in data['order'] if n not in actual]
 data.update(packet=new,status='DRAFT_SOURCE_REPAIR_HOSTED_PENDING',revision_of=old,revision_classification_schema=1)
 for k in ['changed_modules','revised_modules','modified_predecessor_modules']:data[k]=actual
 for k in ['exact_predecessor_modules','unchanged_predecessor_modules','reused_modules']:
  if k in data:data[k]=unchanged
 if 'unchanged_producer_modules' in data:data['unchanged_producer_modules']=unchanged if isinstance(data['unchanged_producer_modules'],list) else len(unchanged)
 data['new_modules']=[]
 for n,row in data['files'].items():row['sha256']=h(dst/n)
 dump(dst/'intake.json',data);ev=dst/'HOSTED-43586414080';ev.mkdir();own=R/'logs'/(lane+'-artifact')/'progress-experiments'/old
 assert json.loads((own/'RESULT.json').read_text())['packet_sha256']==h(src/'intake.json');shutil.copytree(own,ev/'own-hosted');cp(src/'intake.json',ev/'PREDECESSOR-intake.json');shutil.copytree(C,ev/'canonical')
 cp(R/'machine_contracts.py',ev/'machine_contracts.py');cp(Path(__file__),ev/'package_successors.py')
 # Exact authored source reports plus every named preserved source/checker/log binding.
 for bind in reviews:
  cp(bind,ev/'source-reviews'/bind.name);report=V/bind.name.replace('-BINDINGS.json','-REVIEW.md');assert report.exists();cp(report,ev/'source-reviews'/report.name)
  b=json.loads(bind.read_text())
  for rel,digest in b.get('source_bindings',{}).items():assert h(V/rel)==digest,(bind.name,rel);cp(V/rel,ev/'source-reviews'/rel)
 for s in manifest['sources']:
  for proof in s['own_evidence']:
   sp=Path(proof['log_path']);od=ev/'observed-frontiers'/s['module'][:-5]/proof['lane'];cp(sp,od/'FAILURE.log');cp(sp.parent.parent/'RESULT.json',od/'RESULT.json');cp(EX/proof['predecessor']/'intake.json',od/'PREDECESSOR-intake.json');cp(R/'logs'/(proof['lane']+'-ARTIFACT-METADATA.json'),od/'ARTIFACT-METADATA.json')
 caveat='Inherited IntegralOverlapRootGenerators318 retains an earlier proof body versus the geometry closure, with the same public API. It is unchanged; trace stopped in PEL before geometry and no trace geometry pass is claimed.'
 if lane=='trace':
  shutil.copytree(GPK,ev/'geometry-original-packet')
  for gl,gp in [('center','height-normalized-valuative-center-r65'),('lattice','height-original-ks-lattice-assembly-r16')]:
   gsrc=GE/gl/'progress-experiments'/gp;shutil.copytree(gsrc,ev/'geometry-current-corroboration'/gl);cp(GE/(gl+'-artifact.json'),ev/'geometry-current-corroboration'/(gl+'-artifact.json'))
  # Match the exact native source identities in published geometry and older trace.
  for n in GEOM:assert (dst/n).read_bytes()==(GPK/n).read_bytes()
 dump(dst/'COPY-BINDINGS.json',{'predecessor':old,'successor':new,'copies':copies,'unchanged_count':len(unchanged),'full_order_count':len(data['order']),'own_hosted_result_sha256':h(own/'RESULT.json'),'own_predecessor_intake_sha256':h(src/'intake.json'),'trace_dependency_caveat':caveat if lane=='trace' else None})
 text=f'# {new}\n\nSource-level draft successor to `{old}` using own hosted run43586414080 at f89bd0a. Current integration base83851e60 changed only two separate geometry successors/registry; every current PEL predecessor byte is identical.\n\n{len(actual)} exact changed copies: '+', '.join('`'+n+'`' for n in actual)+f'. Full ordered closure {len(data["order"])} modules; {len(unchanged)} byte-identical. Nine machine-readable obligations are scoped to actual propagated sources. Human source contracts, exact native declarations and actual consumers are bound.\n\nThe chosen-pole theorem receives explicit OnePoint infinity annotations, so literal public statement text is not claimed unchanged; intended full domain/conclusion is preserved. Siegel replaces only its two inverse proof bodies with complete coordinatewise cancellation; original maps, positivity telescopes and every later period/theta proof stay unchanged. Quotient changes preserve actual parity.ker classes and all four-bit/five-label domains, without identifying that kernel with scalar/unit equivalence or asserting a geometric deck action.\n\n'
 if lane=='trace':text+='Two geometry files are exact copies of already-published838 sources, independently source-reviewed from original43583139321 diagnostics. Current43588277165 corroboration shows GlobalComparison full-module PASS5.784s, but CommonRestriction full-module FAIL6.226s. Common propagation is explicitly source-only and still failing, not accepted. Original scratch evidence is separate from this later full-module result. Trace has not reached either geometry module. '+caveat+'\n\n'
 text+='No new preventive PEL edits, local Lean/Lake, resource/trust changes, admission, kernel acceptance, complete packet pass or full arithmetic theorem claim. Hosted validation and final audits remain pending.\n';(dst/'README.md').write_text(text)
 obligations=[]
 for idx,key in enumerate(IDS):
  parts=[(n,CONTRACTS[n][0][idx]) for n in actual if n in CONTRACTS];refs=[];evidence=['README.md','HOSTED-43586414080/own-hosted/RESULT.json']
  for n in actual:
   if n not in CONTRACTS:continue
   refs += [n+'.lean','HOSTED-43586414080/canonical/before/'+n+'.lean']
   evidence += ['HOSTED-43586414080/canonical/'+CONTRACTS[n][1],'HOSTED-43586414080/canonical/'+n+'.lean.patch']
  if lane=='trace':
   go=json.loads((GPK/'APPLICATION.json').read_text())['obligations'][idx];assert go['id']==key
   gt=[go[k] for k in ['required_input','constructed_input','justification']]
   if key=='downstream_and_history':gt[1]='Trace retains its full1504-module order. Its exact two propagated geometry sources match published838 center65/lattice16. All other148? sources are determined precisely by COPY-BINDINGS and intake, with no source added or removed.';gt[1]=gt[1].replace('All other148? sources are determined precisely by COPY-BINDINGS and intake,','All remaining sources are classified exactly by COPY-BINDINGS and intake,')
   if key=='verification_boundary':gt[1]+=' Later own43588277165 confirms Global full-module pass5.784s and Common full-module failure6.226s; this trace itself stopped earlier and has no geometry pass.';gt[2]+=' Common remains a failing source-only propagation, not an accepted repair.'
   parts.append(('Published geometry exact propagation',gt));refs += GEOM+['HOSTED-43586414080/geometry-original-packet/APPLICATION.json'];evidence+=['HOSTED-43586414080/geometry-original-packet/README.md','HOSTED-43586414080/geometry-current-corroboration/center/RESULT.json','HOSTED-43586414080/geometry-current-corroboration/lattice/RESULT.json']
  for rel in refs+evidence:assert (dst/rel).is_file(),rel
  obligations.append({'id':key,'required_input':' '.join(n+': '+t[0] for n,t in parts),'constructed_input':' '.join(n+': '+t[1] for n,t in parts),'justification':' '.join(n+': '+t[2] for n,t in parts),'scope_modules':actual,'source_references':refs,'evidence':evidence})
 app={'packet':new,'status':'DRAFT_SOURCE_REPAIR_HOSTED_PENDING','predecessor':old,'source_commit':manifest['observed_head'],'integration_base_commit':manifest['current_integration_head'],'observed_and_current_packet_tree_identical':True,'run_id':43586414080,'claim':'Exact observed PEL repairs plus separately identified published geometry source propagation only where present; all still require hosted trace/packet checking.','local_lean_run':False,'kernel_verified':False,'independently_accepted':False,'full_arithmetic_theorem_proved':False,'resources_changed':False,'public_telescopes_changed':False,'explicit_statement_type_annotations':'ComplexSphereAffineNormalization318' in actual,'modified_predecessor_modules':actual,'new_modules':[],'obligations':obligations,'machine_contract_status':'DRAFT_REQUIRES_INDEPENDENT_PROPAGATION_REVIEW','intake_sha256':h(dst/'intake.json'),'copy_bindings_sha256':h(dst/'COPY-BINDINGS.json'),'sources':{n:h(dst/n) for n in data['files']}}
 if lane=='trace':app.update(trace_dependency_caveat=caveat,geometry_propagation={'original_run':43583139321,'original_head':'bbda4d19e7fa46cf330b59f026f40ca897585a9e','published_head':manifest['current_integration_head'],'current_corroboration_run':43588277165,'global_full_module_pass':True,'common_full_module_pass':False,'common_full_module_still_fails':True,'trace_geometry_reached':False})
 app['bindings']={str(p.relative_to(dst)):h(p) for p in sorted(dst.rglob('*')) if p.is_file() and p.parent!=dst};app['bindings'].update({'README.md':h(dst/'README.md'),'COPY-BINDINGS.json':h(dst/'COPY-BINDINGS.json')});dump(dst/'APPLICATION.json',app)
 prior=OUT/old;prior.mkdir(exist_ok=True)
 for n in ['intake.json',*data['files']]:cp(src/n,prior/n)
 pe.packet(new,plan,OUT);rows.append({'predecessor':old,'successor':new,'lane':lane,'order_count':len(data['order']),'changed':actual,'intake_sha256':h(dst/'intake.json'),'application_sha256':h(dst/'APPLICATION.json')});print('PASS',new,len(data['order']),actual,flush=True)
dump(R/'SUCCESSOR_MAP.json',{'mapping':{a:b for a,b in MAP.values()},'packets':rows,'local_lean_executed':False});assert sum(len(r['changed']) for r in rows)==13
print('All5 source-only drafts ready for independent full propagation/current machine-contract review.')
