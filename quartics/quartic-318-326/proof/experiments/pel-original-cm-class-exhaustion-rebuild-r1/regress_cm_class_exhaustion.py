from pathlib import Path
from itertools import product
from math import isqrt
import json
primes=[2,3,5,7,11,13,17]
assert [p for p in range(2,19) if all(p%d for d in range(2,isqrt(p)+1))]==primes
primepowers=[(p,n,p**n) for p in primes for n in range(1,8) if p**n<=18]
assert all(p<=7 or n==1 for p,n,v in primepowers)
roots={p:[x for x in range(p) if (x*x+210)%p==0] for p in primes}
assert all(roots[p]==[] for p in [11,13,17])
assert all(roots[p]==[0] for p in [2,3,5,7])
words=list(product([False,True],repeat=3))
norms={a:(2 if a[0] else 1)*(3 if a[1] else 1)*(5 if a[2] else 1) for a in words}
assert sorted(norms.values())==[1,2,3,5,6,10,15,30]
for a in words:
 if any(a):
  d=norms[a]
  assert d<210 and isqrt(d)**2!=d and 210%d==0
for a,b in product(words,repeat=2):
 x=tuple(u!=v for u,v in zip(a,b))
 assert (not any(x))==(a==b)
 assert all((int(u)+int(v))%2==int(w) for u,v,w in zip(a,b,x))
# Independent theta-stable full rank lattices, HNF columns (a,0),(b,c).
hnf=[]
for a in range(1,19):
 for c in range(1,19):
  if a*c>18:continue
  for b in range(a):
   if a%c==0 and b%c==0 and (b*b+210*c*c)%(a*c)==0:
    hnf.append((a,b,c))
assert len(hnf)==15
assert sorted(a*c for a,b,c in hnf)==[1,2,3,4,5,6,7,8,9,10,12,14,15,16,18]
# Negative controls: ramified residues do have a root, and theta has norm210.
assert roots[7]==[0]
assert 0**2+210*1**2==210
out={'status':'PASS','prime_power_cases':len(primepowers),'excluded_residues':41,
 'ramified_residue_checks':17,'binary_words':8,'binary_pairs':64,
 'nonprincipal_word_norms':7,'independent_theta_stable_lattices':hnf,
 'negative_controls':2,'scope':'Exact regression, not Lean acceptance or CM reciprocity.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n')
print(out)
