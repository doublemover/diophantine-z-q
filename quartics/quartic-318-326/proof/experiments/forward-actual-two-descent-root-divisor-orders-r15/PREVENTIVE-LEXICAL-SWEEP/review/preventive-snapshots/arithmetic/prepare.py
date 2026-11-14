from pathlib import Path
import json,re,hashlib,difflib,shutil,subprocess
W=Path(__file__).resolve().parent;R=W.parent/'pel-integration43582938856/repo';E=R/'quartics/quartic-318-326/proof/experiments';HEAD='f89bd0a3cb8a788d6c7f2f494a21d7d103a893cb'
packets=['forward-actual-two-descent-root-divisor-orders-r13','forward-original-weighted-weyl-r22-replay-r13'];scanpackets=['contact-original-positive-generators-r74']+packets
pattern=re.compile(r'(?P<op><|≤)(?=i[A-Za-z_])');sha=lambda b:hashlib.sha256(b).hexdigest();nonwhite=lambda s:re.sub(r'\s','',s)
selected=['ScalarSmallPrimePreparation318','FixedArithmeticLabels318','TernaryChartModuli318','OriginalTernaryBasis318','ActualQuarticCoefficientHeight318','ActualQuarticUniformFrame318','ActualQuarticLabelHeight318','ActualGaussianHeightGrowth318','ActualPrimitiveCorrectionProducts318']
assert subprocess.check_output(['git','-C',str(R),'rev-parse','HEAD'],text=True).strip()==HEAD
out=[];patch=[];allhits=[];unique=set()
for packet in scanpackets:
 p=E/packet;d=json.loads((p/'intake.json').read_text())
 for j,n in enumerate(d['order']):
  b=(p/(n+'.lean')).read_bytes();unique.add((n,sha(b)))
  for k,line in enumerate(b.decode().splitlines(),1):
   matches=list(pattern.finditer(line))
   if matches:allhits.append(dict(packet=packet,module=n,order_index=j,line=k,occurrences=len(matches),text=line.strip(),source_sha256=sha(b)))
for n in selected:
 p=E/packets[0]/(n+'.lean');before=p.read_bytes();assert before==(E/packets[1]/(n+'.lean')).read_bytes();assert before==subprocess.check_output(['git','-C',str(R),'show',HEAD+':'+p.relative_to(R).as_posix()]);s=before.decode();t,count=pattern.subn(lambda m:m.group('op')+' ',s);assert count>0 and nonwhite(s)==nonwhite(t)
 folder=W/'candidates'/n;folder.mkdir(parents=True,exist_ok=True);(folder/'before.lean').write_bytes(before);(folder/'after.lean').write_text(t);(folder/'SOURCE.diff').write_text(''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile=n+'.before.lean',tofile=n+'.lean')))
 lines=[];decl=''
 for k,line in enumerate(s.splitlines(),1):
  m=re.search(r'\b(?:lemma|theorem|def)\s+(\w+)',line)
  if m:decl=m.group(1)
  if pattern.search(line):lines.append(dict(line=k,declaration=decl,before=line,after=pattern.sub(lambda m:m.group('op')+' ',line)))
 consumers=[]
 for mod in json.loads((E/packets[0]/'intake.json').read_text())['order']:
  f=E/packets[0]/(mod+'.lean')
  for k,line in enumerate(f.read_text().splitlines(),1):
   if any(re.search(r'\b'+re.escape(x['declaration'])+r'\b',line) for x in lines):consumers.append(dict(module=mod,line=k,text=line.strip()))
 (folder/'REFERENCES.json').write_text(json.dumps(consumers,indent=2)+'\n')
 out.append(dict(module=n,before_sha256=sha(before),after_sha256=sha(t.encode()),inserted_spaces=count,nonwhitespace_bytes_unchanged=True,changes=lines,hosted_failure_observed=False))
 for packet in packets:
  rel='quartics/quartic-318-326/proof/experiments/'+packet+'/'+n+'.lean';patch.extend(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
assert set(h['module'] for h in allhits)==set(selected)|{'ScalarPolePreparation318'}
primary=W/'primary';primary.mkdir(exist_ok=True)
for n in ['Mathlib-Order-InitialSeg.lean','Mathlib-Order-InitialSeg.metadata.json']:
 shutil.copyfile(W.parent/'arithmetic-run43586414080/candidates/primary'/n,primary/n)
(W/'PREVENTATIVE-SOURCE-ONLY.patch').write_text(''.join(patch))
d=dict(head=HEAD,scan_unique_name_hash_pairs=len(unique),selected_modules=len(selected),selected_source_copies=2*len(selected),total_inserted_spaces_per_forward_closure=sum(x['inserted_spaces'] for x in out),all_occurrences=allhits,candidates=out,excluded_observed_module='ScalarPolePreparation318',local_lean_run=False,kernel_verified=False,independently_reviewed=False,production_files_modified=False,successor_metadata_created=False)
(W/'MANIFEST.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({k:v for k,v in d.items() if k not in ['all_occurrences','candidates']},indent=2))
