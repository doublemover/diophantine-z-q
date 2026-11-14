from pathlib import Path
import sys,json,hashlib
B=Path('/workspace/scratch/41c6d5925c0e');R=B/'pel-integration43578868567/repo';W=B/'geometry-run43583139321';O=B/'review43583139321';sys.path.insert(0,str(R/'scripts'));import diagnose_geometry_frontiers as dg
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for lane,packet in [('center','height-normalized-valuative-center-r64'),('lattice','height-original-ks-lattice-assembly-r15')]:
 cfg=dg.CONFIG[packet];src=(R/'quartics/quartic-318-326/proof/experiments'/packet/(cfg['module']+'.lean')).read_text();cases=dg.variants(packet,src);e=W/'evidence'/lane/'progress-experiments'/packet/'scratch-geometry-frontier-diagnostics'
 for n,s in cases.items():assert s==(e/(n+'.lean.txt')).read_text(),(lane,n)
 print('Exact reviewed generator matches all six hosted',lane,'specimens')
for p in (W/'successors').iterdir():
 if not (p/'APPLICATION.json').exists():continue
 a=json.loads((p/'APPLICATION.json').read_text());d=json.loads((p/'intake.json').read_text());inh=json.loads((p/'INHERITANCE.json').read_text());root=p/'HOSTED-43583139321'
 for n in ['IntegralRationalGlobalComparison318','IntegralOriginalCommonRestriction318']:
  if n in d['revised_modules']:assert (p/(n+'.lean')).read_bytes()==(W/'candidates'/(n+'.lean')).read_bytes()
 for n in ['GEOMETRY-GLOBAL-SOURCE-REVIEW.md','GEOMETRY-GLOBAL-SOURCE-BINDINGS.json','GEOMETRY-COMMON-SOURCE-REVIEW.md','GEOMETRY-COMMON-SOURCE-BINDINGS.json']:
  assert sha(root/'reviews'/n)==sha(O/n)
 # Only current review files are compared; historical same-named reports remain historical.
 old=json.loads((root/'PRE-RUNNER-LIMIT-WORDING-APPLICATION.json').read_text());inv={sha(f):str(f.relative_to(p)) for f in p.rglob('*') if f.is_file()}
 for key,h in old['bindings'].items():
  if a['bindings'].get(key)!=h:assert h in inv and inv[h] in a['bindings'],(p.name,key,'missing bound historical bytes')
 assert a['obligations']==old['obligations']
 text=(p/'README.md').read_text();assert 'No runner wall-clock/output limit' in text and 'existing maximum recursion depth' in text
 assert inh['new_sources']==a['sources'];assert len(a['obligations'])==9
 print('PASS exact source copies, reports, nine contracts and wording-correction byte history',p.name,sha(p/'APPLICATION.json'))
print('PASS supplementary provenance; no Lean executed')
