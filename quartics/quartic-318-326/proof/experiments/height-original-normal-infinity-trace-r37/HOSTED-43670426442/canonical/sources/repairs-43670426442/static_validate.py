from pathlib import Path
import sys,json,shutil
r=Path(__file__).resolve().parent;ws=r.parents[1];repo=ws/'integration-20261114/repo';sys.path.insert(0,str(repo/'scripts'))
import check_progress_experiment as e
root=r/'successors';plan=e.ci.derive_plan();out=[]
for row in json.loads((r/'HANDOFF.json').read_text()):
 old=row['old'];p=root/old;p.mkdir(exist_ok=True);src=repo/'quartics/quartic-318-326/proof/experiments'/old
 shutil.copy2(src/'intake.json',p/'intake.json')
 for f in src.glob('*.lean'):shutil.copy2(f,p/f.name)
 _,d,direct,_=e.packet(row['new'],plan,root)
 out.append({'packet':row['new'],'status':'STATIC_PACKET_VALIDATOR_PASS_ONLY','roots':len(d['order']),'required_baseline':len(e.required_baseline(plan,direct)),'local_lean_run':False})
(r/'STATIC-VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
