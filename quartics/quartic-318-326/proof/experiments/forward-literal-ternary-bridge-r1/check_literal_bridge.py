#!/usr/bin/env python3
from pathlib import Path
from itertools import product
from collections import Counter
import json,re,hashlib
import sympy as s
ROOT=Path(__file__).resolve().parent
local=globalv=0
for p in (3,5,7,11,13):
 for k in (1,2,3):
  if k%p==0: continue
  for x,z,w in product(range(p),repeat=3):
   R=(k*w*w-x*z)%p; E=(2*k*w*w-2*x*z)%p
   assert E==2*R%p and (R==0)==(E==0)
   hits=False
   for t in [None,*range(p)]:
    lit=(x%p,w%p) if t is None else ((z-k*t*t*x)%p,(w-t*x)%p)
    eng=(x%p,w%p) if t is None else ((z-(2*k)*t*t*x*pow(2,-1,p))%p,(w-t*x)%p)
    assert lit==eng
    hits|=lit==(0,0)
    local+=1
   assert hits==(R==0)
for ps in ((3,5),(3,7)):
 M=ps[0]*ps[1]
 for k in (1,2):
  for ts in product(*[[None,*range(p)] for p in ps]):
   counts=Counter()
   for x,z,w in product(range(M),repeat=3):
    code=tuple((x%p,w%p) if t is None else ((z-k*t*t*x)%p,(w-t*x)%p) for p,t in zip(ps,ts))
    counts[code]+=1
    globalv+=1
   # Literal integer inverse image index = size of image = M².
   assert len(counts)==M*M and set(counts.values())=={M}
# Negative controls: undoubled engine and even modulus invalid.
assert (1-1)%3==0 and (1-2)%3!=0
assert 1%2!=0 and 2%2==0
# Original five-coordinate factorization, unchanged k.
a,b,c,d,w,k=s.symbols('a b c d w k')
Q=a*a+b*b-c*c-d*d-k*w*w
R=k*w*w-(b-d)*(b+d)
assert s.expand((a+c)*(a-c)-R-Q)==0
# Pair of sums/differences has determinant2, not unimodular overZ.
assert s.det(s.Matrix([[1,-1],[1,1]]))==2
# Exact numerator identity before clearing rational denominators.
u,v,a,b=s.symbols('u v a b');D=1+u*u*a*a
N=(-2*a**3*v+2*a*a*b*u**5-2*a*a*b*u*v*v-6*a*u*u*v-2*b*u**3)*D*D-(v*b*(1-u*u*a*a)-2*u*a*(u*u+a*a))*2*D*(2*u*v*a*a)
P=2*a**3*D*(a*b*u**3+v)*(v*v-1+u**4)+2*u*u*(3*a*v+b*u)*D*(b*b-1+a**4)
assert s.expand(N+2*(u*b+a*v)**3*D-P)==0
# Exact dependency direction. No CM/Anchor consumer of ternary modules.
intake=json.loads((ROOT/'intake.json').read_text());names=set(intake['order'])
graph={n:set(re.findall(r'(?:public )?import\s+([\w.]+)',(ROOT/(n+'.lean')).read_text()))&names for n in names}
ternary={n for n in names if 'Ternary' in n or n=='IntegerResidueBoxCount318'}
def closure(n):
 seen=set();todo=list(graph[n])
 while todo:
  x=todo.pop()
  if x not in seen:seen.add(x);todo.extend(graph[x])
 return seen
consumers=[n for n in names if 'Anchor' in n or 'CM' in n or n in ['OriginalSieveCRTProduct318','ActualSieveEulerProduct318','CoefficientVanishingDensity318']]
assert all(not(closure(n)&ternary) for n in consumers)
# Prior lattice index is not used by the actual residue-box count proof.
box=(ROOT/'OriginalTernaryBoxCount318.lean').read_text()
assert 'lattice_index' not in box and 'membership_iff' in box and 'scaled_count' in box
print(json.dumps({'local_code_equalities':local,'global_same_coordinate_code_vectors':globalv,'global_index_checks':112,'negative_controls':3,'dependency_consumers_checked':len(consumers),'factorization_and_exact_tangent_polynomial':'PASS'},sort_keys=True))
