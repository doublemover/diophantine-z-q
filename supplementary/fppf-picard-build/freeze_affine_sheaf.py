import pathlib,json,hashlib,shutil,datetime,re
root=pathlib.Path('/workspace/scratch/2cb21e4e0864/quartic-proof');p=root/'quartics/quartic-318-326/proof/experiments/affine-sheaf-basechange';b=pathlib.Path('/workspace/shared/affine-sheaf-basechange-final');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
i=json.loads((p/'intake.json').read_text());d=json.loads((p/'DEPENDENCIES.json').read_text());order=i['order']
for n in order:
 assert sha(p/(n+'.lean'))==i['files'][n+'.lean']['sha256']
 assert (b/'lib'/(n+'.olean')).exists()
 log=(b/'logs'/(n+'.txt')).read_text();assert 'LEAN_CHECK_LOCK_ACQUIRED' in log and 'error:' not in log and 'warning:' not in log
match=re.search(r'EXPERIMENT_AUDIT_PASS declarations=(\d+) modules=(\d+)',(b/'logs/audit.txt').read_text());assert match and int(match[2])==len(order);count=int(match[1])
i['status']='STRICT_FRESH_CLOSURE_AND_PRIVATE_AUDIT_PASS';(p/'intake.json').write_text(json.dumps(i,indent=2)+'\n')
(p/'APPLICATION.md').write_text(pathlib.Path('/workspace/shared/fppf-picard-build/affine_sheaf_application.md').read_text())
(p/'README.md').write_text(f'''# Original affine overlaps and candidate coactions

The actual affine scheme pull-push comparison is built from the original
section/pullback comparisons and exact module mate. Actual original line
sheaf morphisms on the full double overlap correspond bijectively to
candidate comonad maps. Actual normalized diagonal evaluation implies the
original comonad counit equation; the geometric triple equation remains open.

Five new sources and five unchanged producers passed a fresh {len(order)}-source
strict replay and private-inclusive recursive audit of {count} declarations,
with no warnings and only propext, Classical.choice and Quot.sound. The
{len(d['baseline_closure'])} baseline predecessors were reused, not rebuilt.
Independent source acceptance remains separate. See APPLICATION.md.
''')
v=p/'validation';v.mkdir(exist_ok=True)
for q in (b/'logs').glob('*.txt'):shutil.copy2(q,v/q.name)
shutil.copy2(b/'ExperimentAudit.lean',v/'ExperimentAudit.lean')
r={'status':'PASS','validated_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Five new sources and five exact producer copies freshly compiled and recursively audited including private/generated declarations. Original affine sheaf comparison, overlap/candidate-map bijection and normalized diagonal counit. No geometric cocycle coalgebra or fppf descent asserted. Verified baseline reused; no independent acceptance.','source_modules':len(order),'new_source_modules':5,'unchanged_producer_modules':5,'audited_declarations':count,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'toolchain':'Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc','mathlib_commit':'56a005855ea17e0b0958f73ec801ae140b0a1679','baseline_commit':d['baseline_commit'],'baseline_snapshot':d['baseline_snapshot'],'verified_predecessors_reused':len(d['baseline_closure']),'predecessors_freshly_rebuilt':0,'commands':[{'module':n,'exit_code':0,'flags':['-j1','-M','6144','-Ddebug.skipKernelTC=false'],'source_sha256':sha(p/(n+'.lean')),'log':n+'.txt','log_sha256':sha(v/(n+'.txt'))} for n in order],'audit':{'exit_code':0,'source':'ExperimentAudit.lean','source_sha256':sha256 if False else sha(v/'ExperimentAudit.lean'),'log':'audit.txt','log_sha256':sha(v/'audit.txt')},'application_sha256':sha(p/'APPLICATION.md'),'intake_sha256':sha(p/'intake.json'),'new_source_acceptance':False,'full_arithmetic_theorem_proved':False}
(v/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');shutil.copy2(p.parent/'original-line-automorphisms/check.sh',p/'check.sh')
for q in [p/'intake.json',v/'receipt.json',p/'APPLICATION.md']:print(sha(q),q)
