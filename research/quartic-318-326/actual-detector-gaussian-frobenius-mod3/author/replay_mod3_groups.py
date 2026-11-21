#!/usr/bin/env python3
"""Finite model checks for the exact mod-3 transfer/prime-selection proof."""
from collections import Counter
from itertools import product
import json

p=3
M=list(product(range(p),repeat=4))
I=(1,0,0,1)
def det(A):a,b,c,d=A;return (a*d-b*c)%p
def tr(A):return (A[0]+A[3])%p
def mul(A,B):
 a,b,c,d=A;x,y,z,t=B
 return ((a*x+b*z)%p,(a*y+b*t)%p,(c*x+d*z)%p,(c*y+d*t)%p)
def inv(A):
 a,b,c,d=A;e=pow(det(A),-1,p)
 return (e*d%p,-e*b%p,-e*c%p,e*a%p)
def close(S):
 P={I};work=[I]
 while work:
  a=work.pop()
  for b in S:
   u=mul(a,b)
   if u not in P:P.add(u);work.append(u)
 return P
def comm(A,B):return mul(mul(mul(A,B),inv(A)),inv(B))
G=[A for A in M if det(A)]
H=[A for A in G if det(A)==1]
assert len(G)==48 and len(H)==24
U=(1,1,0,1); W=(1,0,1,1); D=(2,0,0,1)
assert close([U,W])==set(H) and close([U,W,D])==set(G)
assert comm(D,U)==U and comm(D,W)==W and close([comm(D,U),comm(D,W)])==set(H)
assert (A:= (0,1,1,1)) in G and (det(A),tr(A))==(2,1)
def conjugacy(A):return frozenset(mul(mul(g,A),inv(g)) for g in G)
classes=sorted({(tr(A),len(conjugacy(A)),int(A==I),int(A==(2,0,0,2))) for A in H})
assert classes==[(0,6,0,0),(1,1,0,1),(1,8,0,0),(2,1,1,0),(2,8,0,0)]
good7=1+sum((y*y-x*(x+1)*(x-3))%7==0 for x,y in product(range(7),repeat=2))
assert good7==8 and all((x*x+1)%3 for x in range(3))
out=dict(good7_count=good7,mod3_GL2=len(G),mod3_SL2=len(H),
det_plus_trace_histogram=sorted(Counter(tr(A) for A in H).items()),
det_plus_conjugacy_classes_trace_size_is_I_is_minusI=classes,
scope="Finite checks of the selected residual group and prime class fractions; not a Heegner trace.")
print(json.dumps(out,indent=2,sort_keys=True))
