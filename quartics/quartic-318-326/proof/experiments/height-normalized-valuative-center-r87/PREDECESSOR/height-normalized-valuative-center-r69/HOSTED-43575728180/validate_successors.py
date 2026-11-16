"""Source/metadata validation only. No Lean/Lake/compiler invocation."""
from pathlib import Path
import json,hashlib,tempfile,shutil,sys,copy,re
B=Path(__file__).resolve().parent;R=Path('/workspace/scratch/41c6d5925c0e/pel-integration43572239136/repo');E=R/'quartics/quartic-318-326/proof/experiments'
sys.path.insert(0,str(R/'scripts'));import check_progress_experiment as check
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
plan=check.ci.derive_plan()
with tempfile.TemporaryDirectory(dir=B,prefix='validation-') as temp:
 root=Path(temp)
 for row in json.loads((B/'PAIRS.json').read_text()):
  old,new=row['predecessor'],row['packet'];p=B/'successors'/new;before=E/old;shutil.copytree(p,root/new);(root/old).mkdir()
  for f in [before/'intake.json',*before.glob('*.lean')]:shutil.copyfile(f,root/old/f.name)
  _,d,_,_=check.packet(new,plan,root);prior=json.loads((before/'intake.json').read_text());assert d['order']==prior['order']
  assert set(d['files'])==set(prior['files'])=={f.name for f in p.glob('*.lean')}
  revised=[n for n in d['order'] if (p/(n+'.lean')).read_bytes()!=(before/(n+'.lean')).read_bytes()];reused=[n for n in d['order'] if n not in revised];assert set(revised)==set(row['changed_modules'])
  for k,v in dict(new_modules=[],revised_modules=revised,reused_modules=reused,unchanged_predecessor_modules=reused).items():assert d[k]==v
  a=json.loads((p/'APPLICATION.json').read_text());s={n+'.lean':H(p/(n+'.lean')) for n in d['order']};assert a['sources']==s;assert a['intake_sha256']==H(p/'intake.json') and a['contract_sha256']==H(p/'README.md')
  inh=json.loads((p/'INHERITANCE.json').read_text());assert inh['new_sources']==s and inh['old_sources']=={n+'.lean':H(before/(n+'.lean')) for n in d['order']};assert inh['unchanged_sources']==len(reused)
  for n in revised:
   oldtext=(before/(n+'.lean')).read_text();newtext=(p/(n+'.lean')).read_text();assert re.findall(r'^set_option.*$',oldtext,re.M)==re.findall(r'^set_option.*$',newtext,re.M)
   sigs=lambda text:{m.group(1):m.group(0) for m in re.finditer(r'^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected)\s+)?theorem\s+(\w+).*?:=',text,re.M|re.S)}
   os,ns=sigs(oldtext),sigs(newtext);allowed={'liftOfAlgHomUnit_right'} if n=='IntegralOriginalCommonRestriction318' else set();assert set(ns)==set(os)|allowed;assert all(ns[k]==v for k,v in os.items())
  own='center' if 'center' in new else 'lattice';result=json.loads((p/'HOSTED-43575728180'/(own+'-RESULT.json')).read_text());assert result['packet']==old and result['packet_sha256']==H(before/'intake.json')
  controls=0
  for key in ['new_modules','revised_modules','reused_modules','unchanged_predecessor_modules']:
   bad=copy.deepcopy(d);bad[key]=['__unexpected__'] if key=='new_modules' else []
   try:check.check_revision_classifications(root/new,bad,root)
   except ValueError:controls+=1
   else:raise AssertionError('invalid alias accepted '+key)
  print(json.dumps(dict(packet=new,status='PASS_SOURCE_ONLY',modules=len(d['order']),revised=revised,reused=len(reused),classification_negative_controls=controls)))
