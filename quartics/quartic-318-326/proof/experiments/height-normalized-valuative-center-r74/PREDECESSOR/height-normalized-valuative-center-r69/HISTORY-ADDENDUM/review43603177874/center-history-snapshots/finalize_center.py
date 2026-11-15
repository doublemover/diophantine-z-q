from pathlib import Path
import hashlib,json,shutil
r=Path(__file__).resolve().parent;root=r.parent;p=r/'successors/height-normalized-valuative-center-r69';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();mp=root/'review43603177874/GEOMETRY-PROPAGATION-BINDINGS.json';assert sha(mp)=='96c37a30023311339fb8a05e315cb03fedac6e9f13e0865a1539e6422f705213';m=json.loads(mp.read_text());assert sha(p/'APPLICATION.json')=='b5183c4ab89210a9d346d5cbeb98c6349112ec65027f98eae2904bf8892f7a4a';snap=p/'PROPAGATION-REVIEWED-APPLICATION.json';assert not snap.exists();shutil.copy2(p/'APPLICATION.json',snap)
files=dict(m['reviewer_evidence']);files['review43603177874/GEOMETRY-PROPAGATION-REVIEW.md']='6a443b2ed2454367d4926ebafc86c70115fab48c4f533f56e91f19f02a120c31';files[str(mp.relative_to(root))]=sha(mp)
for n,h in files.items():
 q=root/n;assert sha(q)==h,n;out=p/'PROPAGATION-REVIEW'/n;out.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(q,out)
a=json.loads((p/'APPLICATION.json').read_text());a['status']='SOURCE_AND_PROPAGATION_REVIEWED_HOSTED_KERNEL_PENDING';a['reviewed_application_sha256']=sha(snap);a['propagation_review']={'reviewer':'lean_review_resume','report':'PROPAGATION-REVIEW/review43603177874/GEOMETRY-PROPAGATION-REVIEW.md','report_sha256':files['review43603177874/GEOMETRY-PROPAGATION-REVIEW.md'],'bindings':'PROPAGATION-REVIEW/review43603177874/GEOMETRY-PROPAGATION-BINDINGS.json','bindings_sha256':sha(mp),'scope':'Current source/contract/propagation only; hosted kernel pending'}
for ob in a['obligations']:ob['independent_review']='PASS_CURRENT_CONTRACT_SOURCE_ONLY'
for f in ['SOURCE_VALIDATION.json','HOSTED_REPAIR.json']:
 q=json.loads((p/f).read_text());q['propagation_review']='PASS_SOURCE_AND_CONTRACT_ONLY_HOSTED_PENDING';(p/f).write_text(json.dumps(q,indent=2)+'\n');a['bindings'][f]=sha(p/f)
a['bindings'][snap.name]=sha(snap)
for n,h in files.items():a['bindings']['PROPAGATION-REVIEW/'+n]=h
(p/'APPLICATION.json').write_text(json.dumps(a,indent=2)+'\n')
for n,h in a['bindings'].items():assert sha(p/n)==h,n
allfiles={str(q.relative_to(p)):sha(q) for q in sorted(p.rglob('*')) if q.is_file()};(r/'FINAL-PACKET-FILES.json').write_text(json.dumps(allfiles,indent=2)+'\n')
hand={'status':'FROZEN_SOURCE_CONTRACT_PROPAGATION_REVIEWED_HOSTED_PENDING','predecessor':'height-normalized-valuative-center-r68','packet':p.name,'folder':str(p),'base_commit':'57227e167abe49436d651b932ff75d5bdf9b5898','application_sha256':sha(p/'APPLICATION.json'),'intake_sha256':sha(p/'intake.json'),'readme_sha256':sha(p/'README.md'),'source_sha256':sha(p/'IntegralOriginalBicanonicalRestrictions318.lean'),'reviewed_application_sha256':sha(snap),'propagation_report_sha256':files['review43603177874/GEOMETRY-PROPAGATION-REVIEW.md'],'propagation_manifest_sha256':sha(mp),'final_files_manifest_sha256':sha(r/'FINAL-PACKET-FILES.json'),'local_lean_run':False,'full_module_pass':False,'common_production_changed':False};(r/'FINAL-HANDOFF.json').write_text(json.dumps(hand,indent=2)+'\n');print(json.dumps(hand,indent=2))
