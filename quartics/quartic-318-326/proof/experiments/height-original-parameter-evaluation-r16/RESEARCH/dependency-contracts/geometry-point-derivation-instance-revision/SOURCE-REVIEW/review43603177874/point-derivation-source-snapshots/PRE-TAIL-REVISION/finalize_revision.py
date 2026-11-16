from pathlib import Path
import json,hashlib,shutil,tarfile
r=Path(__file__).resolve().parent;old=r.parent/'geometry-point-derivation-audit';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();a=json.loads((r/'APPLICATION.json').read_text());old_a=json.loads((old/'APPLICATION.json').read_text());history=r/'PRE-INSTANCE-REVISION';assert not history.exists();history.mkdir()
for n in ['APPLICATION.json',*old_a['bindings']]:
 q=old/n;dest=history/n;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(q,dest)
for n,h in old_a['bindings'].items():assert H(history/n)==h,n
assert H(history/'APPLICATION.json')==a['prior_application_sha256']
a['revision']['complete_original_snapshot']='PRE-INSTANCE-REVISION';a['bindings']={str(p.relative_to(r)):H(p) for p in sorted(r.rglob('*')) if p.is_file() and p.name not in ['APPLICATION.json','geometry-point-derivation-instance-revision.tar.gz','ARCHIVE-RECEIPT.json']};a['bindings']['PRE-INSTANCE-REVISION/APPLICATION.json']=H(history/'APPLICATION.json')
# Include nested historical APPs too, without a self-binding of the current APP.
for p in sorted(r.rglob('APPLICATION.json')):
 if p!=r/'APPLICATION.json':a['bindings'][str(p.relative_to(r))]=H(p)
(r/'APPLICATION.json').write_text(json.dumps(a,indent=2)+'\n')
for n,h in a['bindings'].items():assert H(r/n)==h,n
out=r/'geometry-point-derivation-instance-revision.tar.gz';files=[p for p in sorted(r.rglob('*')) if p.is_file() and p.name not in [out.name,'ARCHIVE-RECEIPT.json']]
with tarfile.open(out,'w:gz') as t:
 for p in files:t.add(p,arcname=str(p.relative_to(r)))
with tarfile.open(out,'r:gz') as t:
 for p in files:assert t.extractfile(str(p.relative_to(r))).read()==p.read_bytes()
d={'sha256':H(out),'bytes':out.stat().st_size,'files':len(files),'application_sha256':H(r/'APPLICATION.json'),'sources':a['sources'],'status':a['status']};(r/'ARCHIVE-RECEIPT.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d,indent=2))
