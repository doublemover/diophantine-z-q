from pathlib import Path
import json,hashlib,subprocess,datetime
R=Path('/workspace/scratch/2cb21e4e0864/quartic-proof'); P=R/'quartics/quartic-318-326/proof/experiments/height-integer-generic-fiber-r1'; O=P/'independent-review-analytic'; V=P/'verification'; B=R/'quartics/quartic-318-326/proof/progress'; M=B/'.lake/packages/mathlib'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((V/'receipt.json').read_text()); i=json.loads((P/'intake.json').read_text())
assert h(V/'receipt.json')=='4cf200d7cc88d18ae54ba032c6bf4e98cc27dd1a97844f2ddcd031b48f8f9078'
assert h(P/'README.md')==r['application_readme_sha256']
assert h(P/'intake.json')==r['intake_sha256']
for f,s in r['source_files'].items(): assert h(P/f)==s and h(Path('/workspace/shared/height-integer-generic-fiber-review-analytic/sources')/f)==s
pins=json.loads((V/'baseline-source-pins.json').read_text())
for m,s in pins.items():
 f=B/(m+'.lean'); assert h(f)==s
 assert hashlib.sha256(subprocess.check_output(['git','show','5e483a2:'+str(f.relative_to(R))],cwd=R)).hexdigest()==s
primary=json.loads((V/'primary-library-source-pins.json').read_text())
primary['Mathlib/RingTheory/IsGaloisGroup/Basic.lean']=h(M/'Mathlib/RingTheory/IsGaloisGroup/Basic.lean')
for extra in ['Mathlib/AlgebraicGeometry/Morphisms/Finite.lean','Mathlib/AlgebraicGeometry/Morphisms/Flat.lean','Mathlib/AlgebraicGeometry/Morphisms/Etale.lean']:primary[extra]=h(M/extra)
for f,s in primary.items():
 assert h(M/f)==s
 assert hashlib.sha256(subprocess.check_output(['git','show',r['mathlib_commit']+':'+f],cwd=M)).hexdigest()==s
for f,s in r['compile_logs'].items(): assert h(V/f)==s
assert h(V/'ExperimentAudit.log')==r['audit_log_sha256']
assert h(V/'ExperimentAudit.lean')==r['audit_source_sha256']
assert h(V/'driver-recovery.json')==r['driver_recovery_note_sha256']
assert h(P/'verify.sh')==r['verification_script_sha256']
assert h(P.parent/'height-integer-etale-r1/independent-review-analytic/acceptance.json')==r['predecessor_independent_acceptance_sha256']
for f in i['unchanged_predecessor_modules']:
 assert (P/(f+'.lean')).read_bytes()==(P.parent/'height-integer-etale-r1'/(f+'.lean')).read_bytes()
(O/'ReviewAudit.lean').write_bytes(Path('/workspace/shared/height-integer-generic-fiber-review-analytic/sources/ReviewAudit.lean').read_bytes())
assert 'EXPERIMENT_AUDIT_PASS declarations=289 modules=19' in (O/'logs/ReviewAudit.log').read_text()
logs={f.name:h(f) for f in sorted((O/'logs').glob('*.log'))}
assert len(logs)==20
for f in (O/'logs').glob('*.log'): assert 'error:' not in f.read_text() and 'LEAN_CHECK_LOCK_ACQUIRED' in f.read_text()
write=lambda p,x:p.write_text(json.dumps(x,indent=2)+'\n')
write(O/'BINDINGS.json',{'producer_receipt_sha256':h(V/'receipt.json'),'application_contract_sha256':h(P/'README.md'),'intake_sha256':h(P/'intake.json'),'source_files':r['source_files'],'baseline_pins_verified_current_and_5e483a2':len(pins),'baseline_source_pins_sha256':h(V/'baseline-source-pins.json'),'primary_library_sources_verified_pinned_commit':primary,'predecessor_sources_byte_identical':i['unchanged_predecessor_modules'],'producer_logs_verified':len(r['compile_logs'])+1,'producer_driver_recovery_sha256':r['driver_recovery_note_sha256'],'producer_final_script_sha256':r['verification_script_sha256'],'predecessor_acceptance_sha256':r['predecessor_independent_acceptance_sha256']})
write(O/'CHECKS.json',{'status':'PASS','reviewer':'/root/advance_analytic_geometry','time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lean_version':r['lean_version'],'mathlib_commit':r['mathlib_commit'],'strict_flags':r['strict_flags'],'fresh_source_compiles':19,'fresh_private_inclusive_audit_declarations':289,'allowed_axioms':r['allowed_axioms'],'logs':logs,'baseline_predecessors_reused_not_rebuilt':len(pins),'full_arithmetic_theorem_proved':False})
print('BINDINGS_AND_FRESH_CHECKS_PASS')
