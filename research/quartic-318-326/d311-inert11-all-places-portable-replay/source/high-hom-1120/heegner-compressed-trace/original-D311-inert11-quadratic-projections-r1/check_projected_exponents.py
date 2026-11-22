from collections import Counter
from hashlib import sha256
from pathlib import Path
import json
H=Path(__file__).resolve().parent
J=H.parent/'original-D311-inert11-full-valuation-r1'
assert sha256((J/'SHA256SUMS').read_bytes()).hexdigest()=='b938bf96a9d677895937205383a6ca3cf65795143e08d2e059196360c4ab31f6'
for row in (J/'SHA256SUMS').read_text().splitlines():
 h,f=row.split(maxsplit=1)
 assert sha256((J/f).read_bytes()).hexdigest()==h
T=json.loads((H/'EXACT-D311-P11-PROJECTIONS.json').read_text())
A=[json.loads(x) for x in (H/'EXACT-D311-P11-BOTH-COEFFICIENT-ROWS.ndjson').read_text().splitlines()]
B=[json.loads(x) for x in (J/'EXACT-D311-P11-ALL-ARCS.ndjson').read_text().splitlines()]
assert len(A)==19 and all(len(x)==242 for x in A)
assert [[[a,b,z,w,k] for a,b,z,v,w,k,m in R] for R in A]==B
for o in range(2):
 assert dict(Counter(str((k,m)[o]) for R in A for a,b,z,v,w,k,m in R))==T['depth_histograms'][o]
 assert all(0< (k,m)[o]<5 and type((z,v)[o]) is int for R in A for a,b,z,v,w,k,m in R)
 assert [sum((z,v)[o]*w for a,b,z,v,w,k,m in R) for R in A]==T['coefficient_subtotals'][o]
S=dict(zip((4,7),map(sum,T['coefficient_subtotals'])))
assert S=={4:-20,7:20}
P={(h,5):e for h,e in S.items()};P.update({(h,6):-e for h,e in S.items()})
assert P=={(v['sqrt5'],v['sqrtM']):v['valuation'] for v in T['primes_E']}
N=T['f']*(-T['D']);p=T['prime']
assert 5**2%p==(-N)%p and 4**2%p==5 and pow(6,5,p)==p-1
# E is unramified and degree-two at each place. For a split binary field
# every prime of E contributes 2 times its exponent over the named root.
for j,vv in ((1,(5,6)),(5,(9,2))):
 u={t:0 for t in vv}
 for (h,r),e in P.items():u[(r*(1 if j==1 else h))%p]+=2*e
 assert T['binary_projection'][str(j)]=={'splits':True,'oriented_roots_and_exponents':[[t,u[t]] for t in vv]}
for j in (6,30):
 assert pow((-j*N)%p,5,p)==p-1 and sum(P.values())==0
 assert T['binary_projection'][str(j)]=={'splits':False,'unique_exponent':0}
print('all four oriented E-primes over 11 and all binary projections; only M5 nonzero (−80 at root 9)')
