from pathlib import Path
import json,re
O=Path(__file__).resolve().parent;w=O.parent/'pel-run43597228569/successors';base=json.loads((w/'height-original-normal-infinity-trace-r17/APPLICATION.json').read_text());names=['PELPrimeLatticeResidues318','FourRootNormalizedSignAction318','PELOriginalSiegelCoercivity318'];pat='('+ '|'.join(names)+'): '
def parts(s):
 a=re.split(pat,s);assert a[0]=='';return {a[i]:a[i+1].strip() for i in range(1,len(a),2)}
result={}
for p in sorted(w.glob('*/APPLICATION.json')):
 j=json.loads(p.read_text());assert len(j['obligations'])==9
 for x,y in zip(j['obligations'],base['obligations']):
  assert x['id']==y['id']
  for key in ['required_input','constructed_input','justification']:
   xp=parts(x[key]);yp=parts(y[key]);assert set(xp)==set(x['scope_modules']);assert all(yp[k]==v for k,v in xp.items()),(p,key)
 result[p.parent.name]={'nine_obligations_exact_scope_projection':True,'scope':j['obligations'][0]['scope_modules']}
(O/'PEL-CONTRACT-PROJECTION-CHECK.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
