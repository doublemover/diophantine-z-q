#!/usr/bin/env python3
"""Exact full split Kummer local table on the literal two numerical twists."""
from itertools import product
from math import prod
import json,sys
v=int(sys.argv[1]) if len(sys.argv)>1 else 1
assert v in (1,2,3)
pa=415721
qa,q1,q2=((32687299769,8912209,1185793321),
         (39957649961,8912209,1185793321),
         (26008346369,14000089,2208005089))[v-1]
a,b=pa*qa,q1*q2;D=a*b
T0,Ts,Tt=6,5,3
ps=[-1,2,5,7,11,37,2399,pa,qa,q1]
rs=[0,-32*407*2399**2*D,2399*407**2*D]
def c(n,p):
 assert n
 v=0
 while n%p==0:n//=p;v^=1
 r=pow(n%p,(p-1)//2,p);assert r in (1,p-1)
 return (v,int(r==p-1))
def loc(ds,p):
 bits=[c(n,p) for n in ds]
 return [sum(e<<j for j,(e,_) in enumerate(bits)),sum(u<<j for j,(_,u) in enumerate(bits))]
def table(p):
 Q=[[0,0]]
 for i,y in enumerate(rs):
  rr=[y-z for z in rs]; rr[i]=prod(rr[j] for j in range(3) if j!=i)
  Q.append(loc(rr,p))
 assert len(set(e for e,u in Q))==4
 return Q
R={p:table(p) for p in [11,37,2399,pa,qa,q1,q2]}
oddplaces=[5,7,*R]
col={p:[0 if p==q else c(q,p)[1] for q in ps] for p in oddplaces}
def xors(v,L):
 r=0
 for x,z in zip(v,L):
  if z:r^=x
 return r
out=[]
crtweak=[(0,Ts),(0,Tt),(0,T0),(0,T0)]+[(0,T0,Ts,Tt)]*6
for V in product(*crtweak):
 if V[1]&4 or prod(q for j,q in enumerate(ps) if j!=1 and V[j]&4)%8!=1:continue
 for p,C in col.items():
  vp=V[ps.index(p)] if p in ps else 0
  u=xors(V,C)
  if p==5:ok=not (vp&1 or u&1)
  elif p==7:ok=(bool(u&1)==bool(vp))
  elif p==q2:ok=(u==0 and vp==0)
  else:ok=[vp,u] in R[p]
  if not ok:break
 else:out.append(V)
F=(2399,7*11*37*2399*a,7*11*37*a)
U=(2399*a*q1,2399*q1,a)
V=(11,5*2399,5*11*2399)
basis=[tuple(sum(((n<0) if p==-1 else (n%p==0))<<j for j,n in enumerate(d)) for p in ps) for d in (F,U,V)]
assert len(out)==8 and set(out)=={tuple(xors(col,e) for col in zip(*basis)) for e in product((0,1),repeat=3)}
assert loc([D,b,a],q2)==R[q2][3]  # raw alpha normalizes by torsion at root T
print(json.dumps(dict(a=a,b=b,D=D,integral_chart_roots=rs,mod2_support=ps,
   odd_torsion_tables=R,actual_character_rows=col,basis=[F,U,V],all_normalized_eight_classes=out),indent=2))
