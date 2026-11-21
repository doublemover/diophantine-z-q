#!/usr/bin/env python3
"""Verify exact stored tangent/Hilbert products. Python standard library only."""
from fractions import Fraction as Q
from math import gcd,prod
from hashlib import sha256
from pathlib import Path
import json,sys
variant=int(sys.argv[1]) if len(sys.argv)>1 else 1
assert variant in (1,2)
p=Path(__file__).resolve().parent/f'EXACT-NUMERIC-CASSELS-{variant}.json'
raw=p.read_bytes()
assert sha256(raw).hexdigest()==(
'ec8f51317d2e0e9facde365fa33b36935a619d85d3e4f22951d6b50416a6470e' if variant==1 else '8ac95d1974cc84aa972db629e02c4a08787b1000d4e7ca13e8f34ee3c4fd77b1')
z=json.loads(raw)
pa,qa=415721,163199081
q1,q2=(7497601,25515769) if variant==1 else (16990081,17238721)
a,b,D=z['a'],z['b'],z['D']
assert (a,b,D)==(pa*qa,q1*q2,pa*qa*q1*q2)
e=(Q(0),Q(-32*D,407),Q(D,2399))
U=(2399*a*q1,2399*q1,a)
V=(11,5*2399,5*11*2399)
M=(D,b,a)
PLACE=[2,3,5,7,11,13,17,19,23,29,37,2399,pa,qa,q1,q2]
def valu(x,p):
    x=Q(x)
    if x==0:return 2**20,Q(0)
    n=x.numerator;d=x.denominator;v=0
    while n%p==0:v+=1;n//=p
    while d%p==0:v-=1;d//=p
    return v,Q(n,d)
def ures(x,m):
    return x.numerator*pow(x.denominator,-1,m)%m
def kbit(x,p):
    v,u=valu(x,p)
    if p==2:return (v%2,ures(u,8))
    r=pow(ures(u,p),(p-1)//2,p)
    assert r in (1,p-1)
    return (v%2,int(r==p-1))
def hs(x,y,p):
    u,A=kbit(x,p); v,B=kbit(y,p)
    if p==2:
        parity=((A-1)//2)*((B-1)//2)+u*((B*B-1)//8)+v*((A*A-1)//8)
    else:
        parity=u*v*((p-1)//2)+A*v+B*u
    return -1 if parity%2 else 1
def eq_scale(f,g):
    return all(x*g[0]==y*f[0] for x,y in zip(f,g))
rets=[]
for row,(name,d,d2) in zip(z['rows'],(('alphaU',M,U),('alphaV',M,V),('UV',U,V))):
    assert row['name']==name and row['first']==list(d) and row['second']==list(d2)
    tangent=[]
    for i,tdat in enumerate(row['tangents']):
        ii,j,k,cs,vs=tdat
        assert i==ii and [j,k]==[m for m in range(3) if m!=i]
        assert eq_scale(cs,(d[j],-d[k],e[j]-e[k])) and gcd(*cs)==1 and gcd(*vs)==1
        assert all(vs) and sum(c*v*v for c,v in zip(cs,vs))==0
        tangent.append((i,j,k,[c*v for c,v in zip(cs,vs)]))
    neg=[]
    assert [r[0] for r in row['local_rows']]==PLACE
    for p,sign,W in row['local_rows']:
        if W is None:
            assert all(kbit(y,p)==((0,1) if p==2 else (0,0)) for y in d2) and sign==1
        else:
            x=Q(*W['x']); zs=[Q(*r) for r in W['z']]
            exact2=[(x-y)/c for y,c in zip(e,d)]
            eps=[]
            for h,r2 in zip(zs,exact2):
                # Quantitative Hensel at h certifies an exact root z of
                # Z^2-r2 and the lower bound v(z-h)>=v(f(h))-v(2h).
                err=valu(h*h-r2,p)[0];dv=valu(2*h,p)[0]
                assert h and err>2*dv
                eps.append(err-dv)
            vals=[]; signs=[]
            for i,j,k,c in tangent:
                l=c[0]*zs[j]+c[1]*zs[k]+c[2]
                err=min(valu(c[0],p)[0]+eps[j],valu(c[1],p)[0]+eps[k])
                assert l and err>=valu(l,p)[0]+(3 if p==2 else 1)
                vals.append(l);signs.append(hs(l,d2[i],p))
            assert vals==[Q(*r) for r in W['tans']]
            assert signs==W['sy'] and prod(signs)==sign
        if sign==-1:neg.append(p)
    assert (-1)**len(neg)==row['total']
    rets.append((name,neg,row['total']))
assert [s for _,_,s in rets]==([-1,-1,-1] if variant==1 else [1,1,-1])
print(json.dumps(dict(D=D,full_local_sign_summary=rets),indent=2))
