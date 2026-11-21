#!/usr/bin/env python3
"""Certified degree-two six-jet search modulo N^7 on the fixed actual xi-curve."""
import argparse,hashlib,json,sys
from concurrent.futures import ProcessPoolExecutor
from itertools import islice
from itertools import combinations
from math import gcd,isqrt,lcm,prod
from pathlib import Path
import sympy as sp
from sympy.matrices.normalforms import hermite_normal_form

H=Path(__file__).resolve().parent
SIB=H.parent/'actual-one-I-dual-plane-search-r1'
sys.path.insert(0,str(SIB))
assert hashlib.sha256((SIB/'check_dual_planes.py').read_bytes()).hexdigest()==(
    'a620f76ef66898000cc2e8843f8ffac78eed5614fef9e515bfb42ef7b84450ea')
import check_dual_planes as M
C=M.C
F=C.F
ij=C.ij
forms=sp.Matrix(F)
rem=next((a,b) for a,b in combinations(range(10),2) if forms[:,[a,b]].det())
mon=[i for i in range(10) if i not in rem]
assert len(mon)==8
coords=sp.symbols('a b c d')

def value(q,v):
    return sum(c*v[i]*v[j] for c,(i,j) in zip(q,ij))

def polar(x,y):
    return tuple(a-b-c for a,b,c in zip(C.quad([u+v for u,v in zip(x,y)]),C.quad(x),C.quad(y)))

def jet(rows,p,N,pivot):
    j=next(i for i,a in enumerate(rows[2]) if a)
    l=next(i for i,a in enumerate(rows[3]) if a)
    t=next(i for i in range(4) if i not in (pivot,j,l))
    v0=rows[0].copy()
    r=v0[t]
    def minor(g):return ((g[0][j],g[0][l]),(g[1][j],g[1][l]))
    depth=N*N;required=N**7
    while depth<required:
        u=C.quad(v0)
        assert all(a%depth==0 for a in u)
        a,b=C.lift_2x2(tuple(-v//depth for v in u),minor(C.gradient(v0)),p)
        v0[j]+=depth*a;v0[l]+=depth*b
        depth*=p
    g=C.gradient(v0)
    assert v0[pivot]==1 and 0<=r<N and v0[t]==r
    assert all(z%required==0 for z in C.quad(v0))
    J=[v0]
    for k in range(1,7):
        need=N**(7-k)
        v=[0]*4
        if k==1:v[t]=1
        u=[g[0][t],g[1][t]] if k==1 else [0,0]
        for i in range(1,1+k//2):
            b=C.quad(J[i]) if 2*i==k else polar(J[i],J[k-i])
            u=[x+y for x,y in zip(u,b)]
        a,b=C.lift_2x2(tuple(-z for z in u),minor(g),need)
        v[j],v[l]=a,b
        J.append(v)
        assert all((w[j]*a+w[l]*b+x)%need==0 for w,x in zip(g,u))
    evals=[]
    for k in range(7):
        z=[]
        for i in mon:
            a,b=ij[i]
            z.append(N**k*sum(J[l][a]*J[k-l][b] for l in range(k+1))%required)
        evals.append(z)
    return evals

def ll_dual(eval_rows,N):
    S=N**7
    Z=sp.Matrix([*eval_rows,*(S*sp.eye(8)).tolist()])
    B=hermite_normal_form(Z.T).T
    assert B.shape==(8,8)
    B0=B.inv()
    det=abs(B.det())
    assert det>=N**28 and det%N**28==0 and S**8%det==0
    assert all(x.is_Integer for x in Z*B0)
    Du=B0.T*S
    assert all(x.is_Integer for x in Du)
    L,T=Du.lll_transform()
    assert T.det() in (-1,1) and L==T*Du
    w=min((tuple(int(x) for x in r) for r in L.tolist()),key=lambda w:(sum(map(abs,w)),M.primitive(w)))
    assert all(M.dot(w,e)%S==0 for e in eval_rows)
    return M.primitive(w),isqrt((S-1)//sum(map(abs,w))),int(det//N**28)

def affine_rational(eq,xx):
    if not xx:return [()] if all(e==0 for e in eq) else []
    div=sp.groebner(eq,*xx,order='lex',domain=sp.QQ)
    if any(x.is_number for x in div):
        return []
    assert div.is_zero_dimensional
    ext=[sp.Poly(e,xx[-1],domain=sp.QQ) for e in div if e.free_symbols <= {xx[-1]}]
    assert ext
    poly=ext[0]
    for b in ext[1:]:
        poly=poly.gcd(b)
    ret=[]
    for root in poly.ground_roots():
        ee=[sp.expand(e.subs(xx[-1],root)) for e in div]
        ret.extend((*pt,root) for pt in affine_rational(ee,xx[:-1]))
    return ret

def section(fs):
    ret=[]
    for k in range(4):
        chart=coords[:k]+(sp.Integer(1),)+(sp.Integer(0),)*(3-k)
        eq=[sp.expand(value(q,chart)) for q in fs]
        for pt in affine_rational(eq,coords[:k]):
            raw=(*pt,1,*(0,)*(3-k))
            den=lcm(*(int(sp.denom(z)) for z in raw))
            v=M.primitive([int(z*den) for z in raw])
            assert all(value(q,v)==0 for q in fs)
            ret.append(v)
    assert len(set(ret))==len(ret)<=8
    return sorted(ret)

def synthetic_controls():
    # Eight distinct affine roots / four distinct roots on the coordinate infinity chart.
    q1=(1,0,0,0,1,0,0,-1,0,-1)
    affine=(q1,(1,0,0,0,2,0,0,-4,0,1),(0,0,0,0,0,0,0,1,0,-1))
    infinity=(q1,(25,0,0,0,100,0,0,-73,0,-23),(0,0,0,0,0,0,0,0,0,1))
    r1=section(affine)
    r2=section(infinity)
    assert r1==sorted((1,k,l,n) for k in (-1,1) for l in (-1,1) for n in (-1,1))
    assert r2==sorted((3,k,l,0) for k in (-4,4) for l in (-5,5))
    return [len(r1),len(r2)]

def candidate(item):
    r,p,N,i=item
    ee=jet(r,p,N,i)
    w,B,index=ll_dual(ee,N)
    q=[0]*10
    for j,v in zip(mon,w):q[j]=v
    q=tuple(q)
    assert gcd(*q)==1
    return q,B,index

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--p',type=int,default=59)
    ap.add_argument('--k',type=int,default=1)
    ap.add_argument('--partial',type=int,default=0)
    ap.add_argument('--bound',type=int,default=0)
    ap.add_argument('--force-first-exact',type=int,default=1)
    ap.add_argument('--workers',type=int,default=1)
    a=ap.parse_args()
    assert a.workers>=1
    p,k=a.p,a.k;N=p**k
    assert sp.isprime(p) and p>=5 and C.src["d"]%p and k>=1
    pp=M.points(p)
    if p<=113:assert pp==sorted(C.points_mod_p(p))
    total=len(pp)*(N//p)
    data={};stats=[]
    tasks=((r,p,N,i) for x,i in pp for r in C.neighborhoods(x,i,p,k))
    if a.partial:tasks=islice(tasks,a.partial)
    if a.workers==1:
        computed=list(map(candidate,tasks))
    else:
        with ProcessPoolExecutor(max_workers=a.workers) as ex:
            computed=list(ex.map(candidate,tasks,chunksize=8))
    for q,B,index in computed:
        stats.append(B)
        data[q]=max(data.get(q,0),B)
    n=len(stats)
    if a.bound:
        assert min(stats)>=a.bound
        assert n==total
    primes=[x for x in sp.primerange(5,90) if x!=p and C.src['d']%x]
    points={r:[x for x,_ in M.points(r)] for r in primes}
    exact=[];exclusion={r:0 for r in primes};hits=set();forced=0
    for i,q in enumerate(sorted(data)):
        where=next((r for r,rr in points.items() if not any(value(q,x)%r==0 for x in rr)),None)
        if where and i>=a.force_first_exact:
            exclusion[where]+=1
            continue
        sol=section([*F,q])
        if where:
            forced+=1
            assert not sol
        hits.update(sol)
        exact.append(q)
    print(json.dumps(dict(p=p,k=k,N=N,requested_bound=a.bound,
      lower_coverage=min(stats),full_coverage=(n==total),neighborhood_count=n,total_neighborhoods=total,
      unique_quadric_count=len(data),forced_exact_controls=forced,exact_rational_sections=len(exact),
      exact_section_input_sha256=hashlib.sha256(json.dumps(exact).encode()).hexdigest(),
      points_on_entire_auxiliary_union=sorted(hits),section_coordinate_basis=mon,
      excluded_by_first_prime=exclusion,synthetic_solution_controls=synthetic_controls()),sort_keys=True,indent=2))
if __name__=='__main__':main()
