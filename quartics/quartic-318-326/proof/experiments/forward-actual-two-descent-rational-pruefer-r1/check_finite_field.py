#!/usr/bin/env python3
"""Exact finite-field/group and integer Hensel regressions; no Lean build."""
import json,itertools
primes=[5,7,11,13,17,19,23,29,31,37,41]
C=dict(primes=len(primes),twists=0,elliptic_points=0,full_group_pairs=0,adjusted_root_products=0,quotient_surjections=0,explicit_halves=0,signed_hensel_lifts=0,squareclass_lifts=0)
def add(P,Q,n,p):
 if P is None:return Q
 if Q is None:return P
 x,y=P;z,w=Q
 if x==z and (y+w)%p==0:return None
 m=((3*x*x+4*n*x-3*n*n)*pow(2*y,-1,p) if x==z else (y-w)*pow(x-z,-1,p))%p
 X=(m*m-2*n-x-z)%p
 return X,(-y+m*(x-X))%p
def roots(P,n,p):
 if P is None:return 1,1
 x,y=P
 return ((12*n*n if (x+3*n)%p==0 else x+3*n)%p,(4*n*n if (x-n)%p==0 else x-n)%p)
def chi(a,p):assert a%p;return pow(a,(p-1)//2,p)
def hensel(A,z,p,k=4):
 r=z;mod=p
 for j in range(1,k):
  assert (r*r-A)%mod==0
  t=(-((r*r-A)//mod)*pow(2*r,-1,p))%p
  r+=mod*t;mod*=p
  assert (r*r-A)%mod==0
 return r,mod
for p in primes:
 sq={x*x%p for x in range(1,p)}
 for n in range(1,p):
  points=[None]+[(x,y) for x in range(p) for y in range(p) if (y*y-x*(x-n)*(x+3*n))%p==0]
  S=set(points);C['twists']+=1;C['elliptic_points']+=len(points)
  def klass(P):return tuple(chi(a,p) for a in roots(P,n,p))
  im={klass(P) for P in points};assert im==set(itertools.product([1,p-1],repeat=2));C['quotient_surjections']+=1
  doubled={add(P,P,n,p) for P in points};ker={P for P in points if klass(P)==(1,1)}
  assert doubled==ker and len(points)==4*len(doubled)
  assert len([P for P in points if add(P,P,n,p) is None])==4
  for P,Q in itertools.product(points,repeat=2):
   R=add(P,Q,n,p);assert R in S;C['full_group_pairs']+=1
   for a,b,c in zip(roots(P,n,p),roots(Q,n,p),roots(R,n,p)):
    assert a*b*c%p in sq;C['adjusted_root_products']+=1
  for P in ker:
   if P is None:continue
   x,y=P
   aa=[a for a in range(p) if a*a%p==x]
   bb=[b for b in range(p) if b*b%p==(x-n)%p]
   cc=[c for c in range(p) if c*c%p==(x+3*n)%p]
   witnesses=[(a,b,c) for a,b,c in itertools.product(aa,bb,cc) if (a*b*c+y)%p==0]
   assert witnesses
   for a,b,c in witnesses:
    X=(x+a*b+a*c+b*c)%p;Y=(-(a+b)*(a+c)*(b+c))%p
    assert Y and (X,Y) in S and add((X,Y),(X,Y),n,p)==P;C['explicit_halves']+=1
 for A in range(-50,51):
  for z in range(1,p):
   if (z*z-A)%p==0:
    hensel(A,z,p);C['signed_hensel_lifts']+=1
 for A in range(-12,13):
  for B in range(-12,13):
   if A%p==0 or B%p==0:continue
   for s in range(1,p):
    if (A-B*s*s)%p:continue
    r,mod=hensel(A*B,B*s%p,p)
    t=r*pow(B,-1,mod)%mod
    assert (A-B*t*t)%mod==0 and t%p;C['squareclass_lifts']+=1
print(json.dumps({'status':'PASS','checks':C,'scope':'Full actual finite elliptic group/Kummer cardinality identities and signed integral lifting congruences; no global rational-point existence, Selmer-corank or unconditional all-place conclusion.'},indent=2))
