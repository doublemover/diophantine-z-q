#!/usr/bin/env python3
"""Independent complete norm-shell/paired linear contraction of exact torsion frames.

The modular differential table and validated torsion frames are inputs. This
replays neither author's field/curve/line construction nor the Hecke proof.
Solve for 2u3-u2, apply quaternion conjugation directly in the integral
basis, and evaluate the finite fields by explicit elementary arithmetic.
"""
from collections import Counter
from itertools import product
from math import isqrt
from pathlib import Path
import json
import sys

adata = json.loads(Path(sys.argv[1]).read_bytes())
ddata = json.loads(Path(sys.argv[2]).read_bytes())
b32 = {row[0]: tuple(row[1:]) for row in adata['line_frames']}
vals = {r['i']: tuple(r['actual_normalized_f_32']) for r in ddata['basis_vertices']}
assert len(b32) == len(vals) == 16
I = (1,0,0,1)
def mul2(A,B,n):
    a,b,c,d = A
    e,f,g,h = B
    return ((a*e+b*g)%n,(a*f+b*h)%n,(c*e+d*g)%n,(c*f+d*h)%n)
def add2(A,B,k,n):
    return tuple((a+k*b)%n for a,b in zip(A,B))
def mat(v,bs,n):
    R=(0,0,0,0)
    for k,A in zip(v,bs): R=add2(R,A,k,n)
    return R
def act(A,C,n):
    a,b,c,d=A
    x,y=C
    return ((a*x+b*y)%n, (c*x+d*y)%n)
def line(C):
    x,y=C
    if x%2:return (1,y*pow(x,-1,32)%32)
    return (x*pow(y,-1,32)%32,1)
def conjP(v):
    a,b,c,d=v
    return (a-b,-b,-c+d,d)
def conjW(v):
    a,b,c,d=v
    return (a-d,b+c-d,-c+d,-c)
def partner(label,v):
    C=act(pi,b32[label],32)
    V=conjP(v)
    for j in range(3):
        if line(C) in kb32:return kb32[line(C)],V
        C,V=act(w32,C,32),conjW(V)
    raise AssertionError(C)
def sign(v):
    V=mat(v,b3,3)
    possible=set()
    assert V != (0,0,0,0) and mul2(V,V,3)==(0,0,0,0)
    for x,y in product(range(3),repeat=2):
        X,Y=act(V,(x,y),3)
        c=(x*Y-y*X)%3
        if c:possible.add(c)
    assert possible in ({1},{2})
    return 1 if possible=={1} else -1
def times(a,b):
    x,y=a
    s,t=b
    return ((x*s+2*y*t)%5,(x*t+y*s)%5)
def scale(n,a):return tuple(n*x%5 for x in a)
def dterm(i,v):
    # zeta=(rho-1)/2, c=rho*(v[2]+v[3]*zeta)/3, KS factor 1/12.
    a=times((0,1),((v[2]-3*v[3])%5,3*v[3]%5))
    return scale(1,times(vals[i],a))  # 3*12=36=1 mod 5
def shell(q):
    L=isqrt(3*q)
    for t in range(-isqrt(45*q),isqrt(45*q)+1):
        rem=45*q-t*t
        if rem%5:continue
        for x in range(-L,L+1):
            Δ=rem//5-3*x*x
            if Δ<0:continue
            r=isqrt(Δ)
            if r*r!=Δ:continue
            for y2 in ({-r,r}):
                if (y2+x)%2:continue
                y=(y2+x)//2
                u1, z=divmod(t-2*x+y,3)
                if not z:
                    assert 3*(u1+0) + 2*x-y == t and abs(y)<=L
                    assert (u1+y)%2
                    yield (u1+y,2*u1,2*x,2*y)

w32,g32=map(tuple,adata['omega_and_gamma_mod32'])
w3,g3=map(tuple,adata['omega_and_gamma_mod3'])
b2=(I,w32,g32,mul2(w32,g32,32))
b3=(I,w3,g3,mul2(w3,g3,3))
pi=add2(mul2(g32,add2(I,w32,2,32),32),I,1,32)
assert mul2(pi,pi,32)==add2((0,0,0,0),I,-5,32)
kb32={line(C):i for i,C in b32.items()}
summary=[]
for old in adata['q_shells']:
    q=old['q']
    vectors=list(shell(q))
    assert len(vectors)==len(set(vectors))==old['gross_vectors_on_one_bare_curve']
    model=[]
    for o in old['orientations']:
        a=o['root_on_C32']
        terms={}
        for v in vectors:
            A=mat(((1+v[0])//2,*[c//2 for c in v[1:]]),b2,32)
            for i,C in b32.items():
                if act(A,C,32)==tuple(a*c%32 for c in C):
                    terms[i,v]=(sign(v),dterm(i,v))
        original={(r['label'],tuple(r['v'])):(r['e'],tuple(r['raw_normalized_term'])) for r in o['terms']}
        assert terms==original
        e0=o['base'][2]
        S=tuple(sum(e*d[k] for e,d in terms.values())%5 for k in range(2))
        U=tuple(sum(d[k] for _,d in terms.values())%5 for k in range(2))
        J=scale(((-8)*e0)*pow((-3*q)%5,-1,5),times((0,1),S))
        assert S==tuple(o['signed_raw']) and U==tuple(o['unweighted_control'])
        assert J==(o['based_jet_mod5'],0)
        rem=set(terms)
        hist=Counter()
        while rem:
            key=min(rem)
            fk=partner(*key)
            assert fk!=key and fk in rem and partner(*fk)==key
            e,(x,y)=terms[key]
            e1,(x1,y1)=terms[fk]
            assert e1==-e and x1==x and (y1+y)%5==0
            hist[(2*e*y)%5]+=1
            rem-={key,fk}
        assert sum(hist.values())==len(terms)//2
        assert sum(v for k,v in hist.items() if k)==o['nonzero_signed_Frob_pairs']
        assert sum(k*v for k,v in hist.items())%5==S[1]
        model.append(dict(root=a, terms=len(terms), pairs_by_signed_coordinate=[hist[k] for k in range(5)],
                          raw_W_over_rho=S[1], based_jet=J[0], unsigned=U[0]))
    summary.append(dict(q=q, orientations=model))
first=next(d for d in summary if d['q']==41)
second=next(d for d in summary if d['q']==3881)
assert (second['q']-first['q'])%1920==0
assert all(t['pairs_by_signed_coordinate'][0]==0 and t['raw_W_over_rho'] for t in first['orientations'])
assert all(t['terms']==156 and t['pairs_by_signed_coordinate'][0]==0 and not t['raw_W_over_rho'] for t in second['orientations'])
print(json.dumps(summary,indent=2))
