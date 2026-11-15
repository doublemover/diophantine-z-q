from pathlib import Path
import json,hashlib,shutil,tarfile,difflib
r=Path(__file__).resolve().parent;H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();ap=r/'APPLICATION.json';assert H(ap)=='b2dca8f2db12feedfb7284f56f90ee6b83068c072bc287ba01daceab58782b51';a=json.loads(ap.read_text());history=r/'PRE-TAIL-REVISION';assert not history.exists();history.mkdir()
for n in ['APPLICATION.json',*a['bindings']]:
 p=r/n;q=history/n;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
for n,h in a['bindings'].items():assert H(history/n)==h,n
mods=['FirstOrderCotangentEvaluation318.lean','NormalizedCotangentEvaluation318.lean'];diff=[]
for n in mods:
 p=r/'sources'/n;s=p.read_text()
 if n.startswith('FirstOrder'):
  old='        rw [map_one]\n        rfl';new='        simp only [map_one,TrivSqZeroExt.snd_one]';assert s.count(old)==1
 else:
  old='  rw [FourRootFirstOrderPoint318.lift_polynomial,Polynomial.aeval_X]\n  rfl';new='  rw [FourRootFirstOrderPoint318.lift_polynomial,Polynomial.aeval_X] <;> rfl';assert s.count(old)==2
 t=s.replace(old,new);diff.extend(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='before/'+n,tofile='after/'+n));p.write_text(t)
(r/'TACTIC-TAIL.diff').write_text(''.join(diff));a['sources']={p.name:H(p) for p in sorted((r/'sources').glob('*.lean'))};a['tactic_tail_revision']={'reviewed_prior_application_sha256':H(history/'APPLICATION.json'),'cause':'Source-only prevention of unconditional rfl after a potentially closing rewrite; not a hosted failure','complete_prior_snapshot':'PRE-TAIL-REVISION','public_statement_or_map_change':False}
c=json.loads((r/'FUTURE-CLOSURE.json').read_text());c['new_sources']=a['sources'];(r/'FUTURE-CLOSURE.json').write_text(json.dumps(c,indent=2)+'\n')
readme=(r/'README.md').read_text();readme+='\nA further reviewer-requested tactic-tail correction is recorded in TACTIC-TAIL.diff: map_one uses the exact snd_one projection simp; both coordinate evaluations apply their final rfl conditionally with <;>. This prevents a potentially already-closed rewrite from being followed by an unconditional tactic. It is source-only preventive, not an observed hosted error. PRE-TAIL-REVISION retains every prior bound byte and raw APP. Public statements/maps/domains remain identical.\n';(r/'README.md').write_text(readme)
out=r/'geometry-point-derivation-instance-revision.tar.gz';exclude={'APPLICATION.json',out.name,'ARCHIVE-RECEIPT.json'};a['bindings']={str(p.relative_to(r)):H(p) for p in sorted(r.rglob('*')) if p.is_file() and str(p.relative_to(r)) not in exclude};ap.write_text(json.dumps(a,indent=2)+'\n')
files=[p for p in sorted(r.rglob('*')) if p.is_file() and p.name not in [out.name,'ARCHIVE-RECEIPT.json']]
with tarfile.open(out,'w:gz') as t:
 for p in files:t.add(p,arcname=str(p.relative_to(r)))
with tarfile.open(out,'r:gz') as t:
 for p in files:assert t.extractfile(str(p.relative_to(r))).read()==p.read_bytes()
d={'sha256':H(out),'bytes':out.stat().st_size,'files':len(files),'application_sha256':H(ap),'sources':a['sources'],'status':a['status']};(r/'ARCHIVE-RECEIPT.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d,indent=2))
