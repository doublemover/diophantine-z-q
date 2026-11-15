from pathlib import Path
import hashlib,json,shutil,tarfile
root=Path('/workspace/scratch/41c6d5925c0e');r=root/'geometry-normalized-evaluation-adapter';v=root/'review43611323966';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
afile=r/'APPLICATION.json';before=H(afile);assert before=='609c20fdb43281bafedd2e0d4d61bd7d8bf803089bd9644e6159fb3bf9c54f6d'
report=v/'NORMALIZED-EVALUATION-ADAPTER-REVIEW.md';manifest=v/'NORMALIZED-EVALUATION-ADAPTER-BINDINGS.json'
assert H(report)=='a9fd01cfbadd45e815f13037378ff98b71fc51ff595dd1824dfc1ca7ce8d10fa';assert H(manifest)=='72042b841061a3b0af0a6354e0058b4b91dd0e568cb770b2dd0f37d37f4a9564'
b=json.loads(manifest.read_text());assert b['application_sha256']==before;a=json.loads(afile.read_text())
for n,h in a['bindings'].items():assert H(r/n)==h,n
snapshot=r/'SOURCE-REVIEWED-APPLICATION.json';assert not snapshot.exists();shutil.copy2(afile,snapshot)
d=r/'SOURCE-REVIEW';d.mkdir(exist_ok=True)
new={str(snapshot.relative_to(r)):H(snapshot)}
for p in [report,manifest]:
 q=d/p.name;shutil.copy2(p,q);new[str(q.relative_to(r))]=H(q)
for n,h in b['source_bindings'].items():
 p=root/n;assert H(p)==h,n;q=d/n;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q);assert H(q)==h;new[str(q.relative_to(r))]=h
q=d/'bind_adapter_review.py';shutil.copy2(Path(__file__),q);new[str(q.relative_to(r))]=H(q)
a['status']='INDEPENDENT_SOURCE_CURRENT_RESEARCH_CONTRACT_REVIEWED_NOT_ACTIVE';a['source_review']={'report':str((d/report.name).relative_to(r)),'report_sha256':H(report),'bindings':str((d/manifest.name).relative_to(r)),'bindings_sha256':H(manifest),'reviewed_application_sha256':before,'scope':'Source and current research contract only; no hosted/kernel acceptance or original-section/maximal-model/KS claim.'};a['bindings'].update(new);afile.write_text(json.dumps(a,indent=2)+'\n')
for n,h in a['bindings'].items():assert H(r/n)==h,n
for n,h in a['sources'].items():assert H(r/'sources'/n)==h,n
out=r/'geometry-normalized-evaluation-adapter.tar.gz';files=[p for p in sorted(r.rglob('*')) if p.is_file() and str(p.relative_to(r)) not in [out.name,'ARCHIVE-RECEIPT.json'] and '__pycache__' not in p.parts]
with tarfile.open(out,'w:gz') as t:
 for p in files:t.add(p,arcname=str(p.relative_to(r)))
with tarfile.open(out,'r:gz') as t:
 for p in files:assert t.extractfile(str(p.relative_to(r))).read()==p.read_bytes()
receipt={'sha256':H(out),'bytes':out.stat().st_size,'files':len(files),'application_sha256':H(afile),'reviewed_application_sha256':before,'source_review_sha256':H(report),'status':a['status'],'local_lean_run':False};(r/'ARCHIVE-RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
