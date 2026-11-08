#!/usr/bin/env python3
"""Finite byte/row accounting only; no mathematical correctness decision."""
from pathlib import Path
import json,hashlib,gzip,collections,subprocess
W=Path('/workspace/scratch/2cb21e4e0864'); R=W/'diophantine-z-q'; P=W/'recovery-modular-0358/input-inventory-v13'; O=Path(__file__).parent
H=lambda b: hashlib.sha256(b).hexdigest()
checks=[]
def check(name,ok,detail=None):
 checks.append({'check':name,'pass':bool(ok),'detail':detail}); assert ok,(name,detail)
receipt=json.loads((P/'receipt.json').read_text())
check('target receipt hash',H((P/'receipt.json').read_bytes())=='28eb39bd511dcbed2ae8872051090b6b416cec198c6f71f43464b0598a90f7fb')
for p,h in receipt['sources'].items(): check('packet hash '+p,H((P/p).read_bytes())==h)
pins=json.loads((P/'INPUT-PINS.json').read_text())['pins']
drift=[]
for pin in pins:
 raw=(R/pin['path']).read_bytes()
 if H(raw)!=pin['sha256']:
  frozen=subprocess.check_output(['git','show','09e35ad61946e92561460d93c3e57831ea5e3117:'+pin['path']],cwd=R)
  check('frozen input hash '+pin['path'],H(frozen)==pin['sha256'])
  check('only recorded concurrent drift',pin['path']=='quartics/quartic-318-326/docs/arithmetic.md')
  drift.append({'path':pin['path'],'frozen_sha256':pin['sha256'],'current_sha256':H(raw),'scope':'Concurrent Kato section edits after line1591; PP prefix remains unchanged.'})
  (O/'arithmetic-concurrent.diff').write_bytes(subprocess.check_output(['git','diff','--',pin['path']],cwd=R))
 else: check('input hash '+pin['path'],True)
for kind in ['revision-pp-bindings','order-separation-bindings']:
 for x in json.loads((P/(kind+'.json')).read_text()):
  raw=(R/x['path']).read_bytes(); excerpt=b''.join(raw.splitlines(keepends=True)[x['start_line']-1:x['end_line']])
  check(kind+' v'+str(x['version']),excerpt==(P/x['excerpt_path']).read_bytes())
B=R/'quartics/quartic-318-326'
coverage=json.loads((B/'proof/progress/receipts/completeness-work/row-coverage.json').read_text())
a=json.loads(gzip.decompress((B/'construction/318/raw-ir.json.gz').read_bytes()))
check('row coverage exact ids', [c['row'] for c in coverage['coverage']]==list(range(288)))
check('row coverage exact names',all(c['name']==r['name'] and c['row']==r['id'] for c,r in zip(coverage['coverage'],a['residuals'])))
check('recorded classification counts',dict(collections.Counter(c['obligation'] for c in coverage['coverage']))==coverage['counts'])
ops={'quadratic_assignment':'exact_quadratic_assignment','rational_quotient':'exact_rational_quotient','field_quotient_component':'exact_field_quotient_component'}
check('238 generated rows',len(a['gates'])==238 and len({g['coordinateId'] for g in a['gates']})==238 and len({g['definitionResidualId'] for g in a['gates']})==238)
check('gate classification matches actual operation',all(coverage['coverage'][g['definitionResidualId']]['obligation']==ops[g['operation']] for g in a['gates']))
check('80 free including input',len(a['coordinates'])-len(a['gates'])==80 and len(a['coordinates'])==318)
check('50 structural',len(a['residuals'])-len(a['gates'])==50)
check('three 16-step field chains',all(all('detector'+str(r)+'.normChain.'+str(j)+'.'+str(k) in a['values'] for j in range(16) for k in range(2)) for r in range(3)))
for p,h in coverage['source_hashes'].items():
 if p=='docs/arithmetic.md': continue
 check('historical builder/IR same '+p,H((B/p).read_bytes())==h)
old=(P/'excerpts/arithmetic-e96.md').read_bytes().splitlines(keepends=True); new=(B/'docs/arithmetic.md').read_bytes().splitlines(keepends=True)
check('arithmetic first1258lines unchanged',old[:1258]==new[:1258])
result={'scope':'Hash, excerpt and finite row accounting only. No Lean replay or mathematical acceptance.', 'reviewer':'/root/restart_hodge_gluing','observed_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'checks':checks,'count':len(checks),'all_pass':all(c['pass'] for c in checks),'row_counts':coverage['counts'],'concurrent_drift':drift}
(O/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',len(checks),'finite binding/accounting checks; 288 exact row ids/names, 238 generated, 50 structural, 80 free.')
