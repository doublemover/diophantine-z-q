#!/usr/bin/env python3
"""Exact regression, not a substitute for hosted Lean or an infinitude proof."""
from fractions import Fraction as F
from math import isqrt
import json,itertools

def add(P,Q,n):
 if P is None:return Q
 if Q is None:return P
 x,y=P;z,w=Q
 if x==z and y==-w:return None
 m=(3*x*x+4*n*x-3*n*n)/(2*y) if x==z else (y-w)/(x-z)
 X=m*m-2*n-x-z
 return X,-y+m*(x-X)
def curve(P,n):return P is None or P[1]**2==P[0]*(P[0]-n)*(P[0]+3*n)
def roots(P,n):
 if P is None:return F(1),F(1)
 x,y=P
 return (12*n*n if x==-3*n else x+3*n,4*n*n if x==n else x-n)
def sign(x):return 1 if x>0 else -1
def sq(x):
 return x>=0 and isqrt(x.numerator)**2==x.numerator and isqrt(x.denominator)**2==x.denominator
# Literal arithmetic in Q(sqrt(2)), with the actual rational field embedding.
def q(x):return F(x),F(0)
def qa(x,y):return x[0]+y[0],x[1]+y[1]
def qn(x):return -x[0],-x[1]
def qs(x,y):return qa(x,qn(y))
def qm(x,y):return x[0]*y[0]+2*x[1]*y[1],x[0]*y[1]+x[1]*y[0]
def qi(x):
 d=x[0]*x[0]-2*x[1]*x[1];assert d
 return x[0]/d,-x[1]/d
def qd(x,y):return qm(x,qi(y))
def qadd(P,Q,n):
 if P is None:return Q
 if Q is None:return P
 x,y=P;z,w=Q
 if x==z and y==qn(w):return None
 m=qd(qs(qa(qm(q(3),qm(x,x)),qm(q(4),qm(n,x))),qm(q(3),qm(n,n))),qm(q(2),y)) if x==z else qd(qs(y,w),qs(x,z))
 X=qs(qs(qs(qm(m,m),qm(q(2),n)),x),z)
 return X,qa(qn(y),qm(m,qs(x,X)))
def embed(P):return None if P is None else(q(P[0]),q(P[1]))
def qroots(P,n):
 if P is None:return q(1),q(1)
 x,y=P
 return (qm(q(12),qm(n,n)) if x==qm(q(-3),n) else qa(x,qm(q(3),n)),qm(q(4),qm(n,n)) if x==n else qs(x,n))
counts={'rational_twists':0,'rational_points':0,'actual_group_map_checks':0,'root_coordinate_map_checks':0,'real_kummer_hom_checks':0,'rational_kummer_hom_checks':0,'nested_subgroups':0,'obstruction_class_tests':0}
for ni in range(-18,19):
 if not ni:continue
 n=F(ni);points={None,(F(0),F(0)),(n,F(0)),(-3*n,F(0))}
 for den in [1,2,3,4]:
  for num in range(-45,81):
   x=F(num,den);r=x*(x-n)*(x+3*n)
   if sq(r):
    y=F(isqrt(r.numerator),isqrt(r.denominator));points|={(x,y),(x,-y)}
 points=list(points);counts['rational_twists']+=1;counts['rational_points']+=len(points)
 for P in points:
  assert curve(P,n)
  assert tuple(q(z) for z in roots(P,n))==qroots(embed(P),q(n));counts['root_coordinate_map_checks']+=2
 for P,Q in itertools.product(points,repeat=2):
  R=add(P,Q,n);assert curve(R,n)
  assert embed(R)==qadd(embed(P),embed(Q),q(n));counts['actual_group_map_checks']+=1
  for a,b,c in zip(roots(P,n),roots(Q,n),roots(R,n)):
   assert sq(a*b*c);counts['rational_kummer_hom_checks']+=1
   assert sign(c)==sign(a)*sign(b);counts['real_kummer_hom_checks']+=1
# Exhaust every nested pair of literal subspaces of F_2^3; the quotient is an actual coset quotient.
V=frozenset(range(8))
spaces=[frozenset(S) for r in range(1,9) for S in itertools.combinations(V,r) if 0 in S and all(x^y in S for x in S for y in S)]
assert len(spaces)==16
for A in spaces:
 for L in spaces:
  if not A<=L:continue
  counts['nested_subgroups']+=1
  cosets={frozenset(x^a for a in A) for x in L}
  assert len(cosets)*len(A)==len(L)
  assert (len(cosets)==1)==(A==L)
  for z in L:
   assert (frozenset(z^a for a in A)==A)==(z in A)
   counts['obstruction_class_tests']+=1
print(json.dumps({'status':'PASS','checks':counts,'scope':'Exact field embedding/group/root identities and finite obstruction-quotient analogues; no all-place sufficiency, elliptic Selmer identification, obstruction vanishing or rational infinitude proof.'},indent=2))
