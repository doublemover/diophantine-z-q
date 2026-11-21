#!/usr/bin/env python3
"""Independent scalar-ring replay, using exact affine reduction and generic lift branches."""
import json
import sys
from math import isqrt
from pathlib import Path

packet = Path(sys.argv[1])
loaded = json.loads((packet/'EXACT-SPLIT-SHALLOW-FORMAL-ROWS.json').read_text())
h = int(loaded['actual_h'])

def multiply(a, P, add, zero):
    T=zero
    while a:
        if a&1: T=add(T,P)
        a//=2
        if a: P=add(P,P)
    return T

def finite_sum(p,A,P,Q):
    if P is None: return Q
    if Q is None: return P
    x,y=P
    u,v=Q
    if x==u:
        if (y+v)%p==0: return None
        slope=(3*x*x+A)*pow(2*y,-1,p)
    else:
        slope=(v-y)*pow(u-x,-1,p)
    d=(slope*slope-x-u)%p
    return d,(slope*(x-d)-y)%p

def square_ring(p,A):
    N=p*p
    def shift(P,z):
        if isinstance(P,int): return (P+z)%N
        x,y=P
        return (x+2*y*z)%N,(y+(3*x*x+A)*z)%N
    def finalize(xx,yy,zz):
        if zz%p:
            return xx*pow(zz,-2,N)%N, yy*pow(zz,-3,N)%N
        assert xx%p and yy%p
        return -xx*zz*pow(yy,-1,N)%N
    def chord(P,Q):
        x,y=P
        u,v=Q
        w=(u-x)%N
        k=(v-y)%N
        xx=(k*k-(x+u)*w*w)%N
        yy=(k*(x*w*w-xx)-y*w**3)%N
        return finalize(xx,yy,w)
    def twice(P):
        x,y=P
        w=2*y%N
        k=(3*x*x+A)%N
        xx=(k*k-2*x*w*w)%N
        yy=(k*(x*w*w-xx)-y*w**3)%N
        return finalize(xx,yy,w)
    def add(P,Q):
        if isinstance(P,int): return shift(Q,P)
        if isinstance(Q,int): return shift(P,Q)
        if P==Q: return twice(P)
        x,y=P
        u,v=Q
        if (u-x)%p or (v-y)%p: return chord(P,Q)
        if y%p:
            # P-Q is formal: evaluate via opposite reductions, then translate 2Q.
            z=chord(P,(u,-v%N))
            assert isinstance(z,int) and z%p==0
            return shift(twice(Q),z)
        # P,Q both lift the same rational 2-torsion point T. Hensel lift T.
        e=x%p
        e=(e-p*((e**3+A*e)//p)*pow(3*e*e+A,-1,p))%N
        assert (e**3+A*e)%N==0
        inv=pow(3*e*e+A,-1,N)
        return (y+v)*inv%N
    return add

rows=[]
for row in loaded['split_depth_rows']:
    p=row['p']
    N=p*p
    assert all(p%u for u in range(2,isqrt(p)+1))
    roots=[r for r in range(p) if r*r%p==2]
    assert roots==[a['root'] for a in row['arms']]
    values=[]
    for r,out in zip(roots,row['arms']):
        rr=next(r+i*p for i in range(p) if (r+i*p)**2%N==2)
        A=(-(3-rr)**2)%N
        P=((1+rr)%N,2*rr%N)
        assert (P[1]**2-P[0]**3-A*P[0])%N==0
        reduction=tuple(v%p for v in P)
        total=[0]*(p)
        for y in range(p): total[y*y%p]+=1
        card=1+sum(total[(x**3+A*x)%p] for x in range(p))
        reduced=None
        for order in range(1,card+1):
            reduced=finite_sum(p,A,reduced,reduction)
            if reduced is None: break
        assert card%order==0 and h%order==0
        lifts= square_ring(p,A)
        # No h-truncation or known point-order exponent at all on the finite lift.
        z=multiply(h,P,lifts,0)
        assert isinstance(z,int) and z%p==0
        U=(-2*z)%N
        assert U%p==0 and U%N!=0
        assert (rr,order,z,U)==(out['hensel_root'],out['order'],out['formal_parameter'],out['U_mod_p2'])
        values.append((order,U))
    rows.append((p,values))
print(json.dumps({'full_h_per_prime_and_both_embeddings':rows,'each_w37_valuation':2}))
