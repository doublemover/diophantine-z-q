#!/usr/bin/env python3
import itertools,math,json
from fractions import Fraction as Q
import sympy as s
import mpmath as m
m.mp.dps=80
c=dict(generic_fiber_identities=0,generic_discrepancy_bounds=0,primitive_density=0,original_prime_keys=0,actual_squarefree_events=0,coordinate_primitivity=0,exact_imprimitive_splits=0,actual_imprimitive_bounds=0,primitive_fiber_bounds=0,imprimitive_counterexample=0)
def le(a,b):assert a<=b+m.mpf('1e-65')*max(1,abs(a),abs(b)),(a,b)
def close(a,b):le(abs(a-b),m.mpf('1e-65'))
def eq(k,v):a,b,c0,d,w=v;return a*a+b*b-c0*c0-d*d-k*w*w==0
def forms(gs,v):a,b,c0,d,w=v;return [a*a+b*b+g*w*w for g in gs]
def key(gs,v):return math.prod(abs(x) for x in forms(gs,v))
def weight(gs,v):return m.fprod(m.log(max(1,abs(x))) for x in forms(gs,v))
for kR in range(1,8):
 for size in range(0,9):
  S=list(range(size));ws=[Q((x+1)**2,3) for x in S];rho=lambda x:(x*x+2*x)%kR
  for a in range(kR+1):
   A=set(range(a));f={r:sum((ws[x] for x in S if rho(x)==r),Q(0)) for r in range(kR)}
   ev=sum((ws[x] for x in S if rho(x) in A),Q(0));M=sum(ws,Q(0))/kR
   assert ev==sum(f[r] for r in A)
   assert ev-len(A)*M==sum((f[r]-M for r in A),Q(0));c['generic_fiber_identities']+=1
   assert abs(ev-len(A)*M)<=sum(abs(f[r]-M) for r in A);c['generic_discrepancy_bounds']+=1
for kap,gs in [(1,[0,-1]),(2,[0,-2,1]),(318,[0,-318,1]),(326,[0,-326,2])]:
 for p in [3,5,7]:
  if (2*kap)%p==0:continue
  R=[v for v in itertools.product(range(p),repeat=5) if (v[0]**2+v[1]**2-v[2]**2-v[3]**2-kap*v[4]**2)%p==0 and any(v)]
  A=[v for v in R if key(gs,v)%p==0];g=Q(len(A),len(R));assert len(R)==p**4-1;c['primitive_density']+=1
  for B in [1,2,3]:
   S=[v for v in itertools.product(range(-B,B+1),repeat=5) if eq(kap,v)]
   prim=lambda v:any(x%p for x in v)
   SP=[v for v in S if prim(v)];SI=[v for v in S if not prim(v)]
   ws={v:weight(gs,v) for v in S};mass=sum(ws.values(),m.mpf(0));mp=sum((ws[v] for v in SP),m.mpf(0));mi=sum((ws[v] for v in SI),m.mpf(0))
   event=lambda T:sum((ws[v] for v in T if key(gs,v)%p==0),m.mpf(0))
   gr=m.mpf(g.numerator)/g.denominator
   rem=event(S)-gr*mass;rp=event(SP)-gr*mp;ri=event(SI)-gr*mi
   close(rem,rp+ri);c['exact_imprimitive_splits']+=1
   le(abs(rem),abs(rp)+mi);c['actual_imprimitive_bounds']+=1
   fs={}
   for v in SP:
    r=tuple(x%p for x in v);fs[r]=fs.get(r,m.mpf(0))+ws[v]
   errs=sum((abs(fs.get(r,m.mpf(0))-mp/len(R)) for r in A),m.mpf(0))
   le(abs(rp),errs);c['primitive_fiber_bounds']+=1
   for v in S:
    assert (key(gs,v)%p==0)==any(x%p==0 for x in forms(gs,v));c['original_prime_keys']+=1
    assert (not prim(v))==all(x%p==0 for x in v);c['coordinate_primitivity']+=1
 for B in [1,2]:
  for v in itertools.product(range(-B,B+1),repeat=5):
   if not eq(kap,v):continue
   for F in [[],[3],[5],[3,5],[5,7]]:
    d=math.prod(F)
    assert (key(gs,v)%d==0)==all(key(gs,v)%p==0 for p in F);c['actual_squarefree_events']+=1
# Explicit original imprimitive point: discarding the correction is false.
v=(3,0,3,0,0);g=Q(2,10);w=weight([0,-1],v)
assert eq(1,v) and all(x%3==0 for x in v) and w>0
assert (1-m.mpf(g.numerator)/g.denominator)*w>0;c['imprimitive_counterexample']=1
print(json.dumps({'status':'PASS','precision_digits':80,'checks':c,'scope':'Exact finite original residue/density/event identities and actual weighted primitive/imprimitive decompositions. No residue-fiber equidistribution or primitive-point asymptotic inferred.'},sort_keys=True))
