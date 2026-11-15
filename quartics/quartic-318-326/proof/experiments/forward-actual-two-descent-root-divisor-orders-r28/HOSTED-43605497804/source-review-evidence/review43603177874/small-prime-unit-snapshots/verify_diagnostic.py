from pathlib import Path
import json,hashlib,sys,importlib.util
w=Path(__file__).resolve().parent;r=w.parent/'pel-followup43603177874/repo';ex=r/'quartics/quartic-318-326/proof/experiments';out=w/'descent-evidence/progress-experiments/forward-actual-two-descent-root-divisor-orders-r16';s=out/'scratch-small-prime-decidable'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=json.loads((w/'descent-artifact.json').read_text());assert a['digest']=='sha256:'+sha(w/'descent.zip');assert a['workflow_run']['id']==43605497804;assert a['workflow_run']['head_sha']=='4c5562395a9891e0d79fa5808926ebf9b2781470'
sys.path[:0]=[str(r/'scripts')];spec=importlib.util.spec_from_file_location('small_prime_diag_exact',r/'scripts/diagnose_small_prime_preparation.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
p=ex/mod.PACKET;c=ex/mod.CONTROL_PACKET;d=json.loads((s/'DIAGNOSTIC.json').read_text());result=json.loads((out/'RESULT.json').read_text());intake=json.loads((p/'intake.json').read_text())
assert d['packet']==result['packet']==mod.PACKET;assert d['packet_intake_sha256']==result['packet_sha256']==sha(p/'intake.json')==mod.INTAKE_SHA;assert d['packet_application_sha256']==sha(p/'APPLICATION.json')==mod.APPLICATION_SHA
assert d['full_result_sha256']==sha(out/'RESULT.json');assert d['production_log_sha256']==sha(out/'logs/ScalarSmallPrimePreparation318.log');assert (out/'logs/ScalarSmallPrimePreparation318.log').read_text().strip()=='WALL_CLOCK_LIMIT_EXCEEDED'
idx=intake['order'].index(mod.MODULE);assert [x['module'] for x in result['commands']]==intake['order'][:idx+1];assert all(x['exit_code']==0 for x in result['commands'][:-1]);assert result['commands'][-1]['exit_code']==124
assert d['actual_head']==a['workflow_run']['head_sha'];assert d['strict_flags']==list(mod.EXPECTED_FLAGS);assert d['seconds_per_probe']==90;assert d['bytes_per_probe']==2097152
variants=mod.variants((p/(mod.MODULE+'.lean')).read_text(),(c/(mod.MODULE+'.lean')).read_text());assert [x['variant'] for x in d['variants']]==list(variants)
rows=[]
for row in d['variants']:
 n=row['variant'];text=(s/(n+'.lean.txt')).read_text();log=s/(n+'.log');assert text==variants[n];assert row['source_sha256']==sha(s/(n+'.lean.txt'));assert row['bytes']+(len(('\n'+row['limit']+'\n').encode()) if row['limit'] else 0)==log.stat().st_size;assert row['native_profiler_control_seen'];assert row['admitted'] is False and row['proof_acceptance'] is False
 if n=='abstract_three_unit_control':assert row['exit_code']==0 and row['limit'] is None
 else:assert row['exit_code']==-9 and row['limit']=='SCRATCH_WALL_LIMIT' and log.read_text().rstrip().endswith('SCRATCH_WALL_LIMIT')
 rows.append({'variant':n,'exit_code':row['exit_code'],'seconds':row['seconds'],'limit':row['limit'],'last_marker':next(x for x in reversed(log.read_text().splitlines()) if x.startswith('SMALL_PRIME_'))})
summary={'run':43605497804,'head':a['workflow_run']['head_sha'],'artifact_id':a['id'],'zip_sha256':sha(w/'descent.zip'),'diagnostic_sha256':sha(s/'DIAGNOSTIC.json'),'all_five_exact_specimens_regenerated':True,'ordinary_module':result['commands'][-1],'probes':rows,'no_diagnostic_log_cap':True,'interpretation':'Marked exact context reaches CONVERT_TWO; split context reaches UNIT_2 but not VALUE_2. This is a bounded contextual localization, not full-module acceptance. Abstract units complete in a deliberately different context.','local_lean_run':False,'kernel_verified':False}
(w/'VERIFIED-TARGETED-DIAGNOSTIC.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
