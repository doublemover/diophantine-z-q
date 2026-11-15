from pathlib import Path
import json,hashlib,zipfile,subprocess,re,shutil
B=Path('/workspace/scratch/41c6d5925c0e');W=B/'geometry-run43583139321';O=B/'review43583139321';R=B/'pel-integration43582938856/repo';H='bbda4d19e7fa46cf330b59f026f40ca897585a9e';REL='quartics/quartic-318-326/proof/experiments'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
art={a['id']:a for a in json.loads((O/'independent-artifact-metadata.json').read_text())['artifacts']}
rows=[]
for lane,module,packet,aid in [('center','IntegralRationalGlobalComparison318','height-normalized-valuative-center-r64',14110820388),('lattice','IntegralOriginalCommonRestriction318','height-original-ks-lattice-assembly-r15',14110445870)]:
 p=W/'candidates'/f'{module}.lean';before=p.with_name(p.name+'.before');rp=W/'candidates'/f'{module}-REPAIR.json';j=json.loads(rp.read_text());meta=art[aid];z=W/'evidence'/f'{lane}.zip'
 assert meta['workflow_run']['id']==43583139321 and meta['workflow_run']['head_sha']==H and sha(z)==meta['digest'].split(':')[1]
 assert sha(p)==j['candidate_sha256'] and sha(before)==j['before_sha256']
 assert before.read_bytes()==subprocess.check_output(['git','show',H+':'+REL+'/'+packet+'/'+module+'.lean'],cwd=R)
 ev=W/'evidence'/lane/'progress-experiments'/packet;dg=ev/'scratch-geometry-frontier-diagnostics';d=json.loads((dg/'DIAGNOSTIC.json').read_text());result=json.loads((ev/'RESULT.json').read_text())
 assert sha(ev/'RESULT.json')==j['own_result_sha256']==d['full_result_sha256'];assert sha(dg/'DIAGNOSTIC.json')==j['diagnostic_summary_sha256'];assert result['packet']==packet and result['status']=='FAILED'
 assert result['packet_sha256']==sha(R/REL/packet/'intake.json')==d['packet_intake_sha256'];assert d['original_source_sha256']==sha(before)
 assert d['production_source_changed'] is False and d['full_packet_accepted'] is False and d['baseline_or_experiment_accepted'] is False and len(d['variants'])==6
 assert d['seconds_per_probe']==90 and d['bytes_per_probe']==2097152
 with zipfile.ZipFile(z) as zz:
  for f in ev.rglob('*'):
   if f.is_file(): assert zz.read(f.relative_to(W/'evidence'/lane).as_posix())==f.read_bytes()
 for v in d['variants']:
  src=dg/(v['variant']+'.lean.txt');log=dg/(v['variant']+'.log');assert sha(src)==v['source_sha256'];assert log.stat().st_size==v['bytes'];assert v['admitted'] is False and v['proof_acceptance'] is False and v['limit'] is None
  assert 'GEOMETRY_DIAGNOSTIC '+v['variant'] in log.read_text()
 assert sha(ev/'logs'/f'{module}.log')==j['exact_log_sha256']
 old=before.read_text();new=p.read_text();assert re.findall(r'^.*set_option.*$',old,re.M)==re.findall(r'^.*set_option.*$',new,re.M)
 assert not any(x in new for x in ['sorry','axiom ','GEOMETRY_DIAGNOSTIC','set_option profiler','set_option diagnostics'])
 if lane=='center':
  start='theorem infinity_inverse_square :';end='\ntheorem finite_square :';newproof=new.split(start,1)[1].split(end,1)[0].strip()
  scratch=(dg/'typed_square_final_wrappers.lean.txt').read_text();sproof=scratch.split(start,1)[1].split('\nend '+module,1)[0].strip();assert newproof==sproof
  assert new.split(start,1)[0]==old.split(start,1)[0] and new.split(end,1)[1]==old.split(end,1)[1]
  assert [v['exit_code'] for v in d['variants']]==[0,0,0,0,0,1]
 else:
  start='@[expose] def commonRestriction :';end='\ntheorem common_y :';assert new.split(start,1)[0]==old.split(start,1)[0] and new.split(end,1)[1]==old.split(end,1)[1]
  assert [v['exit_code'] for v in d['variants']]==[0,0,0,0,1,1]
 snap=O/lane;snap.mkdir(exist_ok=True)
 for f in [p,before,p.with_name(p.name+'.diff'),rp,W/'candidates'/f'{module}.log',W/'candidates'/f'{lane}-RESULT.json']:shutil.copy2(f,snap/f.name)
 shutil.copytree(dg,snap/'diagnostics',dirs_exist_ok=True)
 rows.append(dict(lane=lane,module=module,packet=packet,artifact=meta,before_sha256=sha(before),after_sha256=sha(p),own_result_sha256=sha(ev/'RESULT.json'),diagnostic_sha256=sha(dg/'DIAGNOSTIC.json'),variants=d['variants'],local_lean_run=False,full_candidate_hosted_pass=False))
 print('PASS',lane,sha(p),[v['exit_code'] for v in d['variants']])
primary=W/'candidates'/'primary'
for row in json.loads((primary/'PROVENANCE.json').read_text()):
 assert sha(primary/row['file'])==row['sha256']
 if 'repository_path' in row:assert (primary/row['file']).read_bytes()==subprocess.check_output(['git','show',H+':'+row['repository_path']],cwd=R)
shutil.copytree(primary,O/'primary',dirs_exist_ok=True)
(O/'GEOMETRY-SOURCE-CHECK-RECEIPT.json').write_text(json.dumps({'run':43583139321,'head':H,'rows':rows,'local_lean_run':False,'source_only':True},indent=2)+'\n')
print('PASS exact hosted artifacts, diagnostics, transplant/source scope and primary predecessor identities')
