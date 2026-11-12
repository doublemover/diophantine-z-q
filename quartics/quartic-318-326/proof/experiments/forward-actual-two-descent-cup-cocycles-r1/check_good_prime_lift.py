#!/usr/bin/env python3
"""Exhaust actual residue point lifts and retained Kummer classes through p^4."""
import json,itertools
C=dict(primes=0,twists=0,finite_points=0,nonexceptional_lifts=0,exceptional_lifts=0,coordinate_unit_checks=0,unit_pair_lifts=0,beta_lifts=0,support_prime_checks=0)
def hensel(A,z,p,k=4):
 r=z;mod=p
 for j in range(1,k):
  assert (r*r-A)%mod==0
  r+=mod*((-((r*r-A)//mod)*pow(2*r,-1,p))%p);mod*=p
  assert (r*r-A)%mod==0
 return r,mod
def coords(P,n):
 if P is None:return 1,1
 x,y=P
 return (12*n*n if x==-3*n else x+3*n,4*n*n if x==n else x-n)
def finite_coords(P,n,p):
 if P is None:return 1,1
 x,y=P
 return ((12*n*n if (x+3*n)%p==0 else x+3*n)%p,(4*n*n if (x-n)%p==0 else x-n)%p)
def char(a,p):assert a%p;return pow(a,(p-1)//2,p)
for p in [5,7,11,13,17,19,23,29,31]:
 C['primes']+=1
 for n in range(1,p):
  C['twists']+=1;M=p**4
  Ps=[None]+[(x,y) for x in range(p) for y in range(p) if (y*y-x*(x-n)*(x+3*n))%p==0]
  lifts={}
  for P in Ps:
   C['finite_points']+=1
   if P is None:Q=None;C['exceptional_lifts']+=1
   else:
    x,y=P
    if x==0:Q=(0,0);C['exceptional_lifts']+=1
    elif x==n:Q=(n,0);C['exceptional_lifts']+=1
    elif (x+3*n)%p==0:Q=(-3*n,0);C['exceptional_lifts']+=1
    else:
     r,mod=hensel(x*(x-n)*(x+3*n),y,p);assert mod==M
     Q=(x,r);C['nonexceptional_lifts']+=1
   if Q is not None:
    x,y=Q;assert (y*y-x*(x-n)*(x+3*n))%M==0
   AB=coords(Q,n);ab=finite_coords(P,n,p)
   assert tuple(A%p for A in AB)==ab
   assert all(A%p for A in AB);C['coordinate_unit_checks']+=2
   lifts.setdefault(tuple(char(A,p) for A in AB),(Q,AB))
  assert len(lifts)==4
  for a,b in itertools.product(range(1,p),repeat=2):
   Q,AB=lifts[(char(a,p),char(b,p))]
   for A,B in zip(AB,[a,b]):
    s=next(s for s in range(1,p) if (A-B*s*s)%p==0)
    r,mod=hensel(A*B,B*s%p,p);u=r*pow(B,-1,mod)%mod
    assert (A-B*u*u)%mod==0 and u%p
   C['unit_pair_lifts']+=1
   if b==1:C['beta_lifts']+=1
# Literal finite-support split: every dividing prime is in the same original support.
for S in itertools.combinations([5,7,11,13,17,19],3):
 n=1
 for s in S:n*=s
 for mask in range(8):
  beta=1
  for j,s in enumerate(S):
   if mask>>j&1:beta*=s
  assert n%beta==0
  for p in [2,3,5,7,11,13,17,19,23,29,31]:
   assert (n%p!=0 or p in S)
   if n%p!=0:assert beta%p!=0
   C['support_prime_checks']+=1
print(json.dumps({'status':'PASS','checks':C,'scope':'Actual finite elliptic representatives, exceptional derivative conventions, point and unit-class lifts modulo p^4, and exact support splitting. No global obstruction vanishing or rational-point existence.'},indent=2))
