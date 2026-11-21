#!/usr/bin/env python3
"""Certified dual-plane point search on the same actual reduced xi-ring."""
from functools import cache
from itertools import product
from pathlib import Path
from math import gcd,lcm,isqrt
from fractions import Fraction as F
import argparse
import hashlib
import json
import sys
import sympy as sp

H=Path(__file__).resolve().parent
OWNER=H.parent/'actual-one-I-third-cover-reduced-r1'
sys.path.insert(0,str(OWNER))
import check_point_box as C

pinned={
 'check_point_box.py':'32fbc8c814b61aa09adb047091819b4e7cce753b65e04dae5265a0823bf7b3bb',
 'EXACT-CFS-REDUCTION.json':'471e44c360e865278798631d3773cd4e968faa2dfe786037c493f897bdb04531'}
assert all(hashlib.sha256((OWNER/k).read_bytes()).hexdigest()==h for k,h in pinned.items())

# Enumerate all projective points in O(p^2) using one quadratic elimination.
@cache
def points(p):
    sq=[[] for _ in range(p)]
    for x in range(p):sq[x*x%p].append(x)
    ret=[]
    if C.quad((1,0,0,0))[0]%p==C.quad((1,0,0,0))[1]%p==0:
        ret.append(((1,0,0,0),0))
    A,B=(int(x)%p for x in C.quad((1,0,0,0)))
    iv=[0]+[pow(a,-1,p) for a in range(1,p)]
    for ix in range(1,4):
        for xx in product(range(p),repeat=ix-1):
            v=(0,)+xx+(1,)+(0,)*(3-ix)
            c,f=(t%p for t in C.quad(v))
            d,e=(t[0]%p for t in C.gradient(v))
            polys=((A,d,c),(B,e,f))
            if (A,d,c)==(0,0,0):
                a,b,n=B,e,f
            elif (B,e,f)==(0,0,0):
                a,b,n=A,d,c
            elif A or B:
                u,z=(A*e-B*d)%p,(A*f-B*c)%p
                if u:
                    r=-z*iv[u]%p
                    if (A*r*r+d*r+c)%p==(B*r*r+e*r+f)%p==0:
                        ret.append(((r,)+v[1:],ix))
                    continue
                if z:continue
                a,b,n=(A,d,c) if A else (B,e,f)
            else:
                a,b,n=(A,d,c) if d else (B,e,f)
            if a:
                rs=[(t-b)*iv[2*a%p]%p for t in sq[(b*b-4*a*n)%p]]
            elif b:
                rs=[-n*iv[b]%p]
            elif not n:
                rs=range(p)
            else:rs=[]
            for r in rs:
                if all((a*r*r+b*r+n)%p==0 for a,b,n in polys):
                    ret.append(((r,)+v[1:],ix))
    assert len(set(ret))==len(ret)
    return sorted(ret)

def dot(x,y):return sum(a*b for a,b in zip(x,y))

def primitive(w):
    assert any(w)
    g=gcd(*w)
    if next(t for t in w if t)<0:g=-g
    return tuple(int(x//g) for x in w)

def dual_basis(rows,N,pivot):
    v,Nw,r,s=rows
    j=next(i for i,t in enumerate(r) if t)
    l=next(i for i,t in enumerate(s) if t)
    t=next(i for i in range(4) if i not in (pivot,j,l))
    assert v[pivot]==1 and Nw[pivot]==0 and Nw[t]==N
    NN=N*N
    w=[u//N for u in Nw]
    R=[]
    for b,c,h,d in [(1,0,0,0),(0,1,0,0),(0,0,N,0),(0,0,0,NN)]:
        a=[0]*4
        a[j],a[l],a[t]=b,c,h
        if not h:a[t]=(-w[j]*b-w[l]*c+N//2)%N-N//2
        a[pivot]=d
        if not d:a[pivot]=(-dot(a,v)+NN//2)%NN-NN//2
        assert all(dot(a,r)%NN==0 for r in rows)
        R.append(a)
    # In coordinate order (j,l,t,pivot), R is triangular diag(1,1,N,N²),
    # hence exactly N²L* by the known determinant and checked membership.
    return R


def second_jet(rows,N,p,pivot):
    v0=rows[0].copy()
    j=next(i for i,t in enumerate(rows[2]) if t)
    l=next(i for i,t in enumerate(rows[3]) if t)
    t=next(i for i in range(4) if i not in (pivot,j,l))
    def minor(g):return ((g[0][j],g[0][l]),(g[1][j],g[1][l]))
    depth=N*N
    while depth<N**3:
        u=C.quad(v0)
        assert all(a%depth==0 for a in u)
        a,b=C.lift_2x2(tuple(-v//depth for v in u),minor(C.gradient(v0)),p)
        v0[j]+=depth*a;v0[l]+=depth*b
        depth*=p
    g=C.gradient(v0)
    u,v=C.lift_2x2((-g[0][t],-g[1][t]),minor(g),N*N)
    v1=[0]*4;v1[t]=1;v1[j]=u;v1[l]=v
    a,b=C.lift_2x2(tuple(-z for z in C.quad(v1)),minor(g),N)
    v2=[0]*4;v2[j]=a;v2[l]=b
    assert all(z%N**3==0 for z in C.quad(v0))
    assert all(dot(row,v1)%N**2==0 for row in g)
    assert all((dot(row,v2)+z)%N==0 for row,z in zip(g,C.quad(v1)))
    return v0,v1,v2,j,l,t

def jet_dual_basis(rows,N,p,pivot):
    v0,v1,v2,j,l,t=second_jet(rows,N,p,pivot)
    guard=gcd(v2[j],v2[l],N);M=N//guard
    if M==1:ell0,ell1=(1,0),(0,1)
    else:
        if gcd(v2[j]//guard,M)!=1:
            j,l=l,j
        r=-(v2[l]//guard)*pow(v2[j]//guard,-1,M)%M
        ell0,ell1=(M,0),(r,1)
    NN=N**3
    R=[]
    for b,c,h,d in [(*ell0,0,0),(*ell1,0,0),(0,0,N*N,0),(0,0,0,NN)]:
        a=[0]*4
        a[j],a[l],a[t]=b,c,h
        if not h:a[t]=(-dot(a,v1)+N*N//2)%(N*N)-N*N//2
        a[pivot]=d
        if not d:a[pivot]=(-dot(a,v0)+NN//2)%NN-NN//2
        assert dot(a,v2)%N==dot(a,v1)%N**2==dot(a,v0)%N**3==0
        R.append(a)
    # Triangular integer matrix in order (j,l,t,pivot), determinant M·N⁵.
    return R,(v0,[N*a for a in v1],[N*N*a for a in v2]),guard

X,Y=sp.symbols('X Y')
def whole_plane_rational_section(w):
    """Get EVERY rational point on C intersect rational hyperplane w=0."""
    p=max(range(4),key=lambda i:abs(w[i]))
    j=[i for i in range(4) if i!=p]
    t=w[p]
    # Universal homogeneous substitution, then chart [X,Y,1].
    def subst(q):
        r=[None]*4
        for i,c in zip(j,q):r[i]=t*c
        r[p]=-sum(w[i]*c for i,c in zip(j,q))
        return r
    def qr(s):
        return tuple(sp.Poly(x,X,Y,domain=sp.QQ) for x in C.quad(subst(s)))
    a,b=qr([X,Y,1])
    rr=a.resultant(b) # eliminate X; polynomials use ordered generators X,Y.
    assert not rr.is_zero
    candidates=[]
    for y in rr.ground_roots():
        qa,qb=(sp.Poly(q.as_expr().subs(Y,y),X,domain=sp.QQ) for q in (a,b))
        gg=qa.gcd(qb)
        assert not gg.is_zero
        for x in gg.ground_roots():
            candidates.append(subst([x,y,1]))
    fa,fb=qr([X,1,0])
    fx,gx=(sp.Poly(q.as_expr(),X,domain=sp.QQ) for q in (fa,fb))
    gg=fx.gcd(gx)
    assert not gg.is_zero
    for x in gg.ground_roots():
        candidates.append(subst([x,1,0]))
    if C.quad(subst([1,0,0]))==(0,0):
        candidates.append(subst([1,0,0]))
    R=set()
    for pt in candidates:
        D=lcm(*(int(sp.denom(z)) for z in pt))
        q=primitive([int(D*z) for z in pt])
        assert dot(w,q)==0 and C.quad(q)==(0,0)
        R.add(q)
    return sorted(R)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--p',type=int,default=59)
    ap.add_argument('--k',type=int,default=2)
    ap.add_argument('--jet',type=int,default=1,choices=(1,2))
    ap.add_argument('--bound',type=int,default=0)
    args=ap.parse_args();p,k,h=args.p,args.k,args.bound
    assert p>=5 and sp.isprime(p) and C.src['d']%p and k>=1 and h>=0
    # Use allowed fixed primes whose reduction is really good.
    primes=[x for x in list(sp.primerange(5,70)) if x!=p and C.src['d']%x]
    pp=points(p)
    if p<=113:assert pp==sorted(C.points_mod_p(p))
    N=p**k
    dist={}
    coverage=[]
    greater_index=0
    for x,i in pp:
        for rows in C.neighborhoods(x,i,p,k):
            if args.jet==2:
                dual,in_primal,extra=jet_dual_basis(rows,N,p,i)
                S=N**3
                greater_index+=int(extra!=1)
            else:
                dual,in_primal,S=dual_basis(rows,N,i),rows,N*N
            B=sp.Matrix(dual)
            L,T=B.lll_transform()
            assert T.det() in (-1,1) and L==T*B
            w=min((tuple(int(v) for v in row) for row in L.tolist()),
                  key=lambda w:(sum(abs(x) for x in w),primitive(w)))
            assert all(dot(w,r)%S==0 for r in in_primal)
            s=sum(map(abs,w))
            # Entire integer box of this height lies in the chosen plane.
            cap=(S-1)//s
            coverage.append(cap)
            u=primitive(w)
            dist[u]=max(dist.get(u,0),cap)
    if h:assert min(coverage)>=h
    uniform=min(coverage)
    controls={r:[x for x,_ in points(r)] for r in primes}
    exclusion={r:0 for r in primes}
    exact=0;hits=set();hard=[]
    for w in sorted(dist):
        for r,rr in controls.items():
            if not any(dot(w,x)%r==0 for x in rr):
                exclusion[r]+=1
                break
        else:
            solved=whole_plane_rational_section(w)
            hits.update(solved)
            hard.append(w)
            exact+=1
    result=dict(p=p,k=k,N=N,requested_height=h,uniform_height=uniform,
                    neighborhoods=len(coverage),different_planes=len(dist),sources=len(pp),
                    screen_good_primes=primes,excluded_by_first_prime=exclusion,
                    full_exact_plane_sections=exact,
                    surviving_planes_sha256=hashlib.sha256(json.dumps(hard).encode()).hexdigest(),
                    rational_points_on_entire_union=sorted(hits))
    if args.jet==2:result.update(jet=2,nonsaturated_bending_index=greater_index)
    print(json.dumps(result,sort_keys=True,indent=2))
if __name__=='__main__':
    main()
