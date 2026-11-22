from collections import Counter
from pathlib import Path
import json
H=Path(__file__).resolve().parent
A=[json.loads(x) for x in (H/'EXACT-D311-P11-ALL-ARCS.ndjson').read_text().splitlines()]
D=json.loads((H/'EXACT-D311-P11-NAMED-VALUATION.json').read_text())
assert len(A)==19 and all(len(row)==242 for row in A)
direction=[(1,i) for i in range(241)]+[(0,1)]
d0,d1=D['matrix_columns'];l=D['matrix_Weil_Gauss_sign']
for row in A:
 assert [(a,b) for a,b,_,_,_ in row]==direction
 for a,b,z,q,k in row:
  s,t=(a*d0[i]+b*d1[i] for i in range(2))
  h=(a*t-b*s)%241
  assert h and q==l*(1 if pow(h,120,241)==1 else -1)
  assert isinstance(z,int) and 0<=k<D['precision'] and abs(z)<=160*k
assert [sum(z*q for _,_,z,q,_ in row) for row in A]==D['source_subtotals']
assert dict(Counter(str(k) for row in A for *_,k in row))==D['maximum_factor_depth_by_arc']
assert {str(q):sum(z for row in A for a,b,z,w,k in row if w==q) for q in (-1,1)}==D['half_raw_valuations']
assert D['oriented_valuation']==sum(D['source_subtotals'])==-20
print('all 4598 signs and resolved row shape; named valuation -20')
