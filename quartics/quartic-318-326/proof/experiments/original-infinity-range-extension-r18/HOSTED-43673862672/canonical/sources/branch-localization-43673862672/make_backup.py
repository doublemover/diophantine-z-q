from pathlib import Path
import zipfile,hashlib,json,shutil
R=Path(__file__).resolve().parent;W=R.parents[1];shutil.copy2(W/'review-20261114/BRANCH-LOCALIZATION-43673862672-SOURCE-REVIEW.md',R/'INDEPENDENT-REVIEW.md');out=R/'PEL-BRANCH-LOCALIZATION-43673862672-SOURCE-REVIEWED.zip'
with zipfile.ZipFile(out,'w',zipfile.ZIP_DEFLATED,7) as z:
 for p in sorted(R.rglob('*')):
  if p.is_file() and p!=out and p.suffix!='.zip':z.write(p,str(p.relative_to(R)))
with zipfile.ZipFile(out) as z:assert z.testzip() is None;count=len(z.namelist())
d={'path':str(out),'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'bytes':out.stat().st_size,'entries':count};(R/'BACKUP-VERIFICATION.json').write_text(json.dumps(d,indent=2)+'\n');print(d)
