from pathlib import Path
import json,hashlib
P=Path('/workspace/scratch/41c6d5925c0e/review43592150561')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
result={}
for lane,reports in [('ARITHMETIC',['ARITHMETIC-POSITIVE']),('PEL',['PEL-FIRST-TWO','PEL-PRIME']),('PICARD',['PICARD-GLUING','PICARD-FIVE'])]:
 j=json.loads((P/(lane+'-PROPAGATION-CHECK.json')).read_text());result[lane]={}
 for row in j['packets']:
  applicable=reports
  if lane=='PICARD':applicable=[reports[0] if 'gluing' in row['name'] else reports[1]]
  have=set(row['application_bindings'].values());counts={}
  for r in applicable:
   bm=P/(r+'-SOURCE-BINDINGS.json');m=json.loads(bm.read_text());required=set(m['source_bindings'].values())|{sha(bm),sha(P/(r+'-SOURCE-REVIEW.md'))}
   assert required<=have,(row['name'],r,'missing exact reviewer bytes',required-have)
   for n,h in m['source_bindings'].items():assert sha(P/n)==h
   counts[r]=len(required)
  result[lane][row['name']]=counts
print(json.dumps(result,indent=2));(P/'PROPAGATION-REVIEW-EVIDENCE-CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
