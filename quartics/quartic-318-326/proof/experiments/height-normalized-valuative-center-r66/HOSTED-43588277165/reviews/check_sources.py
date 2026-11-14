from pathlib import Path
import hashlib,json,subprocess,zipfile,re
W=Path('/workspace/scratch/41c6d5925c0e');R=W/'geometry-integration43583139321/repo';D=W/'review43588277165';B=W/'geometry-run43588277165';H='83851e60e8b2e42cab7eeb55831b45c41d20f2d5';E='quartics/quartic-318-326/proof/experiments/';pkt='height-normalized-valuative-center-r65';sha=lambda b:hashlib.sha256(b).hexdigest();git=lambda p:subprocess.check_output(['git','-C',str(R),'show',H+':'+p])
def save(n,b):p=D/'source-snapshots'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
art=next(a for a in json.load(open(D/'INDEPENDENT-ARTIFACTS.json'))['structuredContent']['artifacts'] if a['name']=='experiment-'+pkt);assert art['workflow_run']['id']==43588277165 and art['workflow_run']['head_sha']==H
zp=B/'evidence/center.zip';assert sha(zp.read_bytes())==art['digest'][7:];z=zipfile.ZipFile(zp);root=B/'evidence/center/progress-experiments'/pkt
for f in ['RESULT.json','logs/IntegralRationalBranchCoefficients318.log','logs/IntegralRationalGlobalComparison318.log','logs/IntegralRationalFiniteAtlas318.log']:
 p=root/f;nm=[n for n in z.namelist() if n.endswith('/'+pkt+'/'+f)];assert len(nm)==1 and z.read(nm[0])==p.read_bytes();save('hosted/'+f,p.read_bytes())
r=json.loads((root/'RESULT.json').read_text());assert r['packet_sha256']==sha(git(E+pkt+'/intake.json'));assert r['commands'][-1]['module']=='IntegralRationalBranchCoefficients318' and r['commands'][-1]['exit_code']==1
assert next(c for c in r['commands'] if c['module']=='IntegralRationalGlobalComparison318')['exit_code']==0
save('hosted/intake.json',git(E+pkt+'/intake.json'));save('hosted/ARTIFACT.json',(json.dumps(art,indent=2)+'\n').encode())
rows=[]
for kind in ['Branch','Infinity']:
 n='IntegralRational'+kind+'Coefficients318';p=B/'candidates'/f'{n}.lean';a=p.read_bytes();b=git(E+pkt+'/'+n+'.lean');assert b==(B/'candidates'/f'{n}.lean.before').read_bytes();record=json.loads((B/'candidates'/f'{n}-REPAIR.json').read_text());assert sha(a)==record['candidate_sha256'] and sha(b)==record['before_sha256']
 assert a.split(b'  rw [AlgHomDifferential318.map_D]')[0]==b.split(b'  rw [AlgHomDifferential318.map_D,coordinate]')[0]
 old=b.decode();new=a.decode();assert old.count('  rw [AlgHomDifferential318.map_D,coordinate]')==1
 if kind=='Branch':replacement='  rw [AlgHomDifferential318.map_D]\n  change KaehlerDifferential.D ℚ (ContactIntrinsicFrames318.BranchRing c i)\n    (branchEquiv c i (IntegralBranchCoordinates318.sourceCoordinate ℚ c i)) = _\n  exact congrArg (KaehlerDifferential.D ℚ (ContactIntrinsicFrames318.BranchRing c i))\n    (coordinate c i)'
 else:replacement='  rw [AlgHomDifferential318.map_D]\n  change KaehlerDifferential.D ℚ (InfinityOpenChart318.OpenOrder c)\n    (rationalOrderEquiv c (IntegralInfinityChart318.coordinate ℚ c)) = _\n  exact congrArg (KaehlerDifferential.D ℚ (InfinityOpenChart318.OpenOrder c))\n    (coordinate c)'
 assert new==old.replace('  rw [AlgHomDifferential318.map_D,coordinate]',replacement)
 save(n+'/before.lean',b);save(n+'/after.lean',a);save(n+'/REPAIR.json',(B/'candidates'/f'{n}-REPAIR.json').read_bytes());rows.append(record)
paths=subprocess.check_output(['git','-C',str(R),'ls-tree','-r','--name-only',H,'--','quartics/quartic-318-326/proof']).decode().splitlines()
for p in (B/'candidates/primary').glob('*.lean'):
 raw=p.read_bytes();assert any(git(q)==raw for q in paths if q.endswith('/'+p.name)),p.name;save('primary/'+p.name,raw)
(D/'SOURCE-CHECK.json').write_text(json.dumps(dict(status='PASS',candidates=rows,head=H,run=43588277165,own_artifact=art,local_lean_run=False,kernel_verified=False),indent=2)+'\n');print('PASS exact observed Branch and preventive Infinity source deltas, original public statements/options, own hosted provenance and primary published producer/consumer identity; no Lean')
