from pathlib import Path
import json,hashlib,subprocess,zipfile,shutil,re
B=Path('/workspace/scratch/41c6d5925c0e');W=B/'pel-run43603177874';O=B/'review43603177874';R=B/'pel-integration43597228569/repo';H='57227e167abe49436d651b932ff75d5bdf9b5898'; sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
P=W/'candidates/primary';prov=json.loads((P/'PROVENANCE.json').read_text())
for n,v in prov.items():
 p=P/n;b=p.read_bytes();assert sha(p)==v['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==v['git_blob']
 if v['repository']=='doublemover/diophantine-z-q':assert b==subprocess.check_output(['git','show',v['commit']+':'+v['path']],cwd=R)
 else:assert v['commit']=='56a005855ea17e0b0958f73ec801ae140b0a1679'
for key in ['THETA','SIGNS','RESIDUE']:
 mp=W/'candidates'/f'{key}-MANIFEST.json';m=json.loads(mp.read_text());n=m['module'];bf=W/'candidates/before'/f'{n}.lean';af=W/'candidates/after'/f'{n}.lean';b=bf.read_text();a=af.read_text();assert m['base']==H and m['run']==43603177874 and sha(bf)==m['before_sha256'] and sha(af)==m['after_sha256'];assert not m['local_lean_run'] and not m['hosted_candidate_pass']
 if key=='THETA':
  assert a.count('include hτ in\n')==5
  assert a.replace('include hτ in\n','').replace('| *S','|*S')==b
  assert m['public_telescopes_changed']
 elif key=='SIGNS':assert a.replace('←pow_two,←map_mul,double_scalar_square','←pow_two,double_scalar_square')==b and not m['public_telescopes_changed']
 else:
  head='theorem residue_lift';tail='theorem residue_surjective'
  assert a.split(head)[0]==b.split(head)[0] and a.split(tail)[1]==b.split(tail)[1]
  assert a.split(head)[1].split(':= by')[0]==b.split(head)[1].split(':= by')[0]
  coeff=re.findall(r'have \w+ : (-?)\(?(\d+) : ZMod (\d+)\)? = (\d+) := by decide',a)
  assert len(coeff)==13,coeff
  assert all(((-1 if sign else 1)*int(v))%int(p)==int(t) for sign,v,p,t in coeff)
  assert 'native_decide' not in a and not m['public_telescopes_changed']
  assert '<;> ring\n' in a and '<;> ring_nf <;>' in a
 files={str(mp.relative_to(W)):sha(mp),**m['source_bindings']};evidence=[]
 for e in m['evidence']:
  files.update(e['files']);lane=e['lane'];packet=e['packet'];rel='quartics/quartic-318-326/proof/experiments/'+packet
  assert bf.read_bytes()==subprocess.check_output(['git','show',H+':'+rel+'/'+n+'.lean'],cwd=R)
  ip=W/'logs'/f'{lane}-published-intake.json';assert ip.read_bytes()==subprocess.check_output(['git','show',H+':'+rel+'/intake.json'],cwd=R)
  meta=json.loads((W/'logs'/f'{lane}-artifact.json').read_text());zp=W/'logs'/f'{lane}.zip'
  assert meta['id']==e['artifact_id'] and meta['workflow_run']['id']==43603177874 and meta['workflow_run']['head_sha']==H and meta['digest']=='sha256:'+sha(zp)
  with zipfile.ZipFile(zp) as z:
   assert z.testzip() is None
   for f in z.namelist():
    if not f.endswith('/'): assert (W/'logs'/f'{lane}-artifact'/f).read_bytes()==z.read(f)
  result=json.loads((W/'logs'/f'{lane}-artifact/progress-experiments'/packet/'RESULT.json').read_text());assert result['packet_sha256']==sha(ip);assert result['commands'][-1]['module']==n and result['commands'][-1]['exit_code']==1;assert all(c['exit_code']==0 for c in result['commands'][:-1]);evidence.append({'artifact':meta['id'],'zip_sha256':sha(zp),'last_command':result['commands'][-1]})
 for rel,h in files.items():assert sha(W/rel)==h,rel
 S=O/f'pel-{key.lower()}-source-snapshots';S.mkdir(exist_ok=True)
 for rel in files:
  dest=S/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(W/rel,dest)
 d={'status':'PASS_SOURCE_AND_CURRENT_HUMAN_NINE_PART_CONTRACT_ONLY','module':n,'before_sha256':sha(bf),'after_sha256':sha(af),'manifest_sha256':sha(mp),'public_telescopes_changed':m['public_telescopes_changed'],'run':43603177874,'head':H,'evidence':evidence,'primary_blob_provenance_checked':len(prov),'source_bindings':{str(p.relative_to(B)):sha(p) for p in S.rglob('*') if p.is_file()},'local_lean_run':False,'candidate_hosted_pass':False,'packet_propagation_review_pending':True}
 (O/f'PEL-{key}-SOURCE-CHECK.json').write_text(json.dumps(d,indent=2)+'\n');print('PASS',key,n,sha(af),'exact source inverse/scope; own artifacts/intakes; pinned primary blobs; current human contract')
