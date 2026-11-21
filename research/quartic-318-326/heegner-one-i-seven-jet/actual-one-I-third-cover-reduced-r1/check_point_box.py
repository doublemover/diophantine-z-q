#!/usr/bin/env python3
"""Exact two-quadric point search via Hensel-linearized lattices and rational sphere enumeration."""
from itertools import product
from fractions import Fraction as Q
from math import gcd,isqrt
from pathlib import Path
import json,argparse
import sympy as sp
H=Path(__file__).resolve().parent
src=json.loads((H/'EXACT-CFS-REDUCTION.json').read_text())
F=src['reduced']
ij=tuple((i,j) for i in range(4) for j in range(i,4))

def quad(x):
    bs=[x[i]*x[j] for i,j in ij]
    return tuple(sum(a*b for a,b in zip(q,bs)) for q in F)

def lift_2x2(s,B,p):
    (a,b),(c,d)=B
    t=pow((a*d-b*c)%p,-1,p)
    return ((d*s[0]-b*s[1])*t%p,(-c*s[0]+a*s[1])*t%p)

def gradient(x):
    ret=[]
    for f in F:
        g=[0]*4
        for a,(i,j) in zip(f,ij):
            g[i]+=a*x[j]
            g[j]+=a*x[i]
        ret.append(g)
    return ret

def points_mod_p(p):
    # Last nonzero coordinate normalized to 1: no projective double count.
    ret=[]
    for i in range(4):
        for pre in product(range(p),repeat=i):
            x=pre+(1,)+(0,)*(3-i)
            if all(v%p==0 for v in quad(x)):ret.append((x,i))
    return ret

def neighborhoods(P,ix,p,k):
    N=p**k
    ix0=[j for j in range(4) if j!=ix]
    g=gradient(P)
    j,l=next((j,l) for j in ix0 for l in ix0 if j<l and (g[0][j]*g[1][l]-g[0][l]*g[1][j])%p)
    free=next(t for t in ix0 if t not in (j,l))
    b=((g[0][j],g[0][l]),(g[1][j],g[1][l]))
    for t in range(P[free],N,p):
        # Fix the free coordinate at its literal value through p^(2k), solve other 2.
        v=list(P);v[free]=t
        pk=p
        while pk<N*N:
            e=quad(v)
            assert all(a%pk==0 for a in e)
            he=lift_2x2(tuple(-a//pk for a in e),b,p)
            v[j]+=pk*he[0];v[l]+=pk*he[1]
            pk*=p
        assert v[ix]==1 and all(x%(N*N)==0 for x in quad(v))
        # Tangent solution modulo N to variation in free coordinate (pivot fixed).
        g1=gradient(v)
        a,c=lift_2x2((-g1[0][free],-g1[1][free]),((g1[0][j],g1[0][l]),(g1[1][j],g1[1][l])),N)
        w=[0]*4;w[free]=1;w[j]=a;w[l]=c
        vv1=[0]*4;vv1[j]=N*N
        vv2=[0]*4;vv2[l]=N*N
        yield [v,[N*u for u in w],vv1,vv2]

def dot(a,b):return sum(x*y for x,y in zip(a,b))

def gs(L):
    norm=[];G=[[None]*4 for _ in range(4)];mu=[[0]*4 for _ in range(4)]
    for i in range(4):
        q=list(L[i])
        for j in range(i):
            mu[i][j]=Q(dot(L[i],G[j]),norm[j])
            q=[x-mu[i][j]*y for x,y in zip(q,G[j])]
        G[i]=q
        norm.append(dot(q,q))
    return norm,mu

def sphere(L,S):
    norm,mu=gs(L)
    coeffs=[0]*4
    def scan(i,rest):
        if i<0:
            yield tuple(sum(coeffs[j]*L[j][k] for j in range(4)) for k in range(4))
            return
        ctr=sum(coeffs[j]*mu[j][i] for j in range(i+1,4))
        aa,bb=ctr.numerator,ctr.denominator
        t=isqrt((rest*bb*bb//norm[i]))
        lo=-((t+aa)//bb);hi=(t-aa)//bb
        for c in range(lo,hi+1):
            coeffs[i]=c
            rr=rest-(c+ctr)**2*norm[i]
            assert rr>=0
            yield from scan(i-1,rr)
    return scan(3,Q(S))

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--prime',type=int,default=59)
    parser.add_argument('--k',type=int,default=2)
    parser.add_argument('--bound',type=int,default=25000)
    a=parser.parse_args();p,k,h=a.prime,a.k,a.bound
    assert p>=5 and sp.isprime(p) and src["d"]%p and k>=1 and h>=1
    P=points_mod_p(p)
    seen={}
    hist={"box_primitive_candidates_including_signs":0,"short_vectors_including_zero":0,
          "smooth_residue_classes":0,"depth_neighborhoods":0}
    for x,ix in P:
        g=gradient(x)
        assert any((g[0][j]*g[1][ell]-g[0][ell]*g[1][j])%p
                   for j in range(4) for ell in range(j+1,4) if j!=ix and ell!=ix)
        hist["smooth_residue_classes"]+=1
        for B in neighborhoods(x,ix,p,k):
            # sympy returns exact [T]∈GL4(Z); verify before enumerating.
            B=sp.Matrix(B);U,T=B.lll_transform()
            assert T.det() in (1,-1) and U==T*B
            hist["depth_neighborhoods"]+=1
            for v in sphere(U.tolist(),4*h*h):
                hist["short_vectors_including_zero"]+=1
                if max(map(abs,v))>h or gcd(*v)!=1:continue
                hist["box_primitive_candidates_including_signs"]+=1
                if quad(v)!=(0,0):continue
                s=next(t for t in v if t);vv=v if s>0 else tuple(-t for t in v)
                assert vv not in seen or seen[vv]==(x,ix);seen[vv]=(x,ix)
    out=dict(prime=p,k=k,bound=h,rational_vectors=sorted(seen),**hist)
    print(json.dumps(out,sort_keys=True,indent=2))
if __name__=='__main__':main()
