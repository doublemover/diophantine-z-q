from pathlib import Path
import sys,json,hashlib,subprocess,zipfile,re,shutil,importlib.util
B=Path('/workspace/scratch/41c6d5925c0e');W=B/'arithmetic-run43605497804';P=W/'candidates';R=B/'pel-followup43603177874/repo';O=B/'review43603177874';H='4c5562395a9891e0d79fa5808926ebf9b2781470';REL='quartics/quartic-318-326/proof/experiments';N='ScalarSmallPrimePreparation318.lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def gh(p):return subprocess.check_output(['git','show',H+':'+p],cwd=R)
a=json.loads((P/'BINDINGS.json').read_text());assert sha(P/N)==a['candidate_sha256']=='6903b836d5f5a08954574cc67bfb9981ddba7ab60b9bb3b973362450da82c2e3';assert sha(P/'APPLICATION.md')==a['human_contract_sha256']=='fdfec49211f0c39f2bac9ae2e630019f72a68b473f5bd06845ecd8278f13c2b8'
for p,h in a['bindings'].items():assert sha(W/p)==h,(p,'binding')
before=(P/('descent.before.'+N)).read_text();after=(P/N).read_text();start=after.index('/-- The elementary unit facts');end=after.index('lemma actual_multiplier_values',start);helper=after[start:end];formula=helper[helper.index('private lemma multiplier_units'):].rstrip();inverse=after[:start]+after[end:];inverse=inverse.replace('  have hu := multiplier_units k₂ k₃ k₁₇\n','')
for t in ['hu.2.1','hu.2.2','hu.1']:inverse=inverse.replace(t,'(by omega)')
assert inverse==before;assert re.findall(r'^\s*set_option.*$',before,re.M)==re.findall(r'^\s*set_option.*$',after,re.M);assert 'SMALL_PRIME_' not in after and 'profiler' not in after
records={}
for lane,packet,zname,eroot in [('descent','forward-actual-two-descent-root-divisor-orders-r16','descent.zip','descent-evidence'),('weighted','forward-original-weighted-weyl-r22-replay-r16','weighted-retry.zip','weighted-logs')]:
 for fn in ['intake.json','APPLICATION.json',N]:assert (P/(lane+'.before.'+fn)).read_bytes()==gh(f'{REL}/{packet}/{fn}'),(lane,fn,'Git')
 meta=json.loads((W/(lane+'-artifact.json')).read_text());assert meta['workflow_run']['id']==43605497804 and meta['workflow_run']['head_sha']==H and meta['digest']=='sha256:'+sha(W/zname)
 with zipfile.ZipFile(W/zname) as z:
  assert z.testzip() is None
  for fn in z.namelist():
   if not fn.endswith('/'):assert (W/eroot/fn).read_bytes()==z.read(fn),(lane,fn,'extraction')
 ep=W/eroot/'progress-experiments'/packet;res=json.loads((ep/'RESULT.json').read_text());intake=json.loads((P/(lane+'.before.intake.json')).read_text());assert res['packet_sha256']==sha(P/(lane+'.before.intake.json'));idx=intake['order'].index(N[:-5]);assert [x['module'] for x in res['commands']]==intake['order'][:idx+1];assert all(x['exit_code']==0 for x in res['commands'][:-1]);assert res['commands'][-1]['exit_code']==124 and (ep/'logs'/N.replace('.lean','.log')).read_text().strip()=='WALL_CLOCK_LIMIT_EXCEEDED'
 records[lane]={'artifact':meta,'result_sha256':sha(ep/'RESULT.json'),'last_command':res['commands'][-1]}
for p in (P/'primary').iterdir():
 rel=f'{REL}/forward-actual-two-descent-root-divisor-orders-r16/{p.name}' if p.suffix=='.lean' else 'scripts/'+p.name
 assert p.read_bytes()==gh(rel),(p.name,'primary Git identity')
sys.dont_write_bytecode=True;sys.path.insert(0,str(R/'scripts'));sp=importlib.util.spec_from_file_location('review_small_prime',R/'scripts/diagnose_small_prime_preparation.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
control=gh(f'{REL}/{m.CONTROL_PACKET}/{N}').decode();variants=m.variants(before,control);S=W/'descent-evidence/progress-experiments'/m.PACKET/'scratch-small-prime-decidable';diag=json.loads((S/'DIAGNOSTIC.json').read_text());assert list(variants)==[x['variant'] for x in diag['variants']];assert diag['actual_head']==H and diag['seconds_per_probe']==90 and diag['bytes_per_probe']==2097152 and diag['strict_flags']==list(m.EXPECTED_FLAGS)
for row in diag['variants']:
 n=row['variant'];f=S/(n+'.lean.txt');l=S/(n+'.log');assert f.read_text()==variants[n] and sha(f)==row['source_sha256'];assert row['native_profiler_control_seen'] and row['admitted'] is False and row['proof_acceptance'] is False;assert row['bytes']+(len(('\n'+row['limit']+'\n').encode()) if row['limit'] else 0)==l.stat().st_size
 if n=='abstract_three_unit_control':assert row['exit_code']==0 and row['limit'] is None and row['seconds']==1.334
 else:assert row['exit_code']==-9 and row['limit']=='SCRATCH_WALL_LIMIT'
abstract=variants['abstract_three_unit_control'];match=re.search(r'lemma diagnostic_abstract_units .*?constructor <;> omega',abstract,re.S);assert match and formula==match.group().replace('lemma diagnostic_abstract_units','private lemma multiplier_units')
assert 'SMALL_PRIME_TACTIC_CONVERT_TWO' in (S/'exact_prefix3_tactic_markers.log').read_text();assert 'SMALL_PRIME_TACTIC_UNIT_2' in (S/'split_unit_value_convert_prefix3.log').read_text() and 'SMALL_PRIME_TACTIC_VALUE_2' not in (S/'split_unit_value_convert_prefix3.log').read_text()
# Actual nondivisibility follows from residues 1 mod2,1 mod3,8 mod17, for all integers.
assert 8%2==0 and 1%2!=0 and 3%3==0 and 1%3!=0 and 17%17==0 and 8%17!=0
snap=O/'small-prime-unit-snapshots';snap.mkdir(exist_ok=True)
for p,h in a['bindings'].items():
 dest=snap/p;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(W/p,dest)
shutil.copy2(P/'BINDINGS.json',snap/'BINDINGS.json')
check={'status':'PASS_SOURCE_HUMAN_CONTRACT_ONLY','candidate_sha256':sha(P/N),'before_sha256':sha(P/('descent.before.'+N)),'human_contract_sha256':sha(P/'APPLICATION.md'),'head':H,'run':43605497804,'exact_inverse':True,'helper_formula_body_exact_completed_control':True,'original_public_statements_and_other_proofs_unchanged':True,'options_unchanged':True,'diagnostic_all_five_exact_specimens':True,'own_evidence':records,'diagnostic':diag,'source_bindings':{str(p.relative_to(B)):sha(p) for p in snap.rglob('*') if p.is_file()},'local_lean_run':False,'production_timeout_resolved':False,'kernel_verified':False}
(O/'SMALL-PRIME-UNITS-SOURCE-CHECK.json').write_text(json.dumps(check,indent=2)+'\n');print('PASS: exact inverse; closed helper matches completed abstract control; all five specimens regenerated; both authentic r16 timeouts verified; same public inputs/coefficient/values/consumers. No full-module pass.')
