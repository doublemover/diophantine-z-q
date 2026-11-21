#!/usr/bin/env python3
"""Exact 120-symbol level-75 real-period ratio, using stdlib only."""
from fractions import Fraction as Q
from functools import cache
from math import gcd,isqrt
import json

N=75
units=[u for u in range(N) if gcd(u,N)==1]
@cache
def key(c,d):
    c,d=c%N,d%N
    assert gcd(c,d,N)==1
    return min((u*c%N,u*d%N) for u in units)
P=sorted({key(c,d) for c in range(N) for d in range(N) if gcd(c,d,N)==1})
PI={z:i for i,z in enumerate(P)}
assert len(P)==120
@cache
def idx(c,d):
    return PI[key(c%N,d%N)]
INF=None

def add(rel,A):
    r=[0]*len(P)
    for z,v in A:r[z]+=v
    if any(r):rel.append(r)

def rat(a,b):
    return Q(a,b) if b else INF

def eg(a,b):
    if b==0:return a,1,0
    g,u,v=eg(b,a%b)
    return g,v,u-(a//b)*v

def rep(c,d):
    if c==0:c=N
    for i in range(N):
        dd=d+i*N
        if gcd(c,dd)==1:break
    else:raise AssertionError((c,d))
    g,a,b=eg(dd,c)
    assert g==1 and a*dd+b*c==1 and key(c,dd)==key(c,d)
    return rat(-b,dd),rat(a,c)

@cache
def endpoint(a):
    if a is INF:return ()
    n,d=a.numerator,a.denominator
    prev,cur=(0,1),(1,0)
    ans=[]
    while d:
        h,n,d=n//d,d,n%d
        z=(h*cur[0]+prev[0],h*cur[1]+prev[1])
        det=z[0]*cur[1]-cur[0]*z[1]
        assert abs(det)==1
        ans.append(idx(det*z[1],cur[1]))
        prev,cur=cur,z
    assert Q(*cur)==a
    return tuple(ans)

def hecke_paths(a,b,l):
    for j in range(l+1):
        def T(x):
            if x is INF:return INF
            return l*x if j==l else (x+j)/l
        yield T(a),T(b)

def trace(l):
    # Literal low curve J_5: y^2=x(x+80)(x+125).
    squares={x*x%l:1 if x==0 else 2 for x in range(l)}
    return l-sum(squares.get(x*(x+80)*(x+125)%l,0) for x in range(l))


def rank_mod(rows,p):
    basis={}
    for row in rows:
        v=[x%p for x in row]
        for i in range(len(P)):
            if not v[i]:continue
            if i not in basis:
                z=pow(v[i],-1,p)
                basis[i]=[t*z%p for t in v]
                break
            b=basis[i];w=v[i]
            for k in range(i,len(P)):
                v[k]=(v[k]-w*b[k])%p
    return len(basis)

def eigensymbol():
    rows=[]
    for c,d in P:
        i=idx(c,d)
        add(rows,[(i,1),(idx(d,-c),1)])
        add(rows,[(i,1),(idx(d,-c-d),1),(idx(-c-d,c),1)])
        add(rows,[(i,1),(idx(-c,d),-1)])
    ranks=[rank_mod(rows,1009)]
    for l in (7,11,13):
        e=trace(l)
        for i,z in enumerate(P):
            a,b=rep(*z)
            C=[(i,-e)]
            for x,y in hecke_paths(a,b,l):
                C.extend((j,1) for j in endpoint(y))
                C.extend((j,-1) for j in endpoint(x))
            add(rows,C)
        ranks.append(rank_mod(rows,1009))
    J=[8, -8, 0, -16, -8, -16, -9, -8, -8, -8, 0, -3, -8, -8, 0, 0, 1, 0, 0, 8, 16, 7, 8, 0, 0, -8, 0, 0, 8, 8, 0, 3, 0, 8, 0, 8, 5, 8, 16, 16, 8, 5, 8, 0, 8, 0, 3, 0, 8, 8, 0, 0, -8, 0, 0, 8, 7, 16, 8, 0, 0, 1, 0, 0, -8, -8, -3, 0, -8, -8, -8, -9, -16, -8, -16, 0, 8, -8, -8, -3, -8, 0, -1, -8, 8, -8, 0, 0, 8, -3, 8, -8, 8, 8, 8, 0, 8, -1, -8, -8, 8, 9, -5, 3, -7, 1, 3, 3, 1, -7, 3, -5, 9, -1, -3, -1, -3, 0, 0, -8]
    assert ranks==[108,117,117,119]
    assert gcd(*J)==1 and all(sum(a*b for a,b in zip(row,J))==0 for row in rows)
    return J,ranks

def leg(a,p):
    z=pow(a%p,(p-1)//2,p)
    return z if z<=1 else -1

def coeff(D):
    val=0
    for z in range(-isqrt(23*D//15),isqrt(23*D//15)+1):
        a=23*D-15*z*z
        for y in range(-isqrt(a//15),isqrt(a//15)+1):
            r=a-15*y*y
            u=isqrt(r)
            if u==0 or u*u!=r or (u-z)%2!=0:continue
            f=(10*u+15*y)%23
            val+=leg(u,3)*leg(f if f else y,23)
    return val

def cusp(r):
    if r is None:return (N,0)
    a,c=r.numerator,r.denominator
    t=gcd(c,N);m=gcd(t,N//t)
    return (t,(a*(c//t))%m)

def main():
    J,ranks=eigensymbol()
    graph=[(cusp(a),cusp(b),J[i]) for i,z in enumerate(P) for a,b in [rep(*z)]]
    C={u for a,b,_ in graph for u in (a,b)}
    t={cusp(None):0}
    for _ in range(len(C)):
        for a,b,v in graph:
            if a in t and b not in t:t[b]=t[a]+v
            if b in t and a not in t:t[a]=t[b]-v
    assert len(t)==len(C)
    G=gcd(*(v-t[b]+t[a] for a,b,v in graph))
    w=sum(J[j] for j in endpoint(Q(0)))

    # All four theta primes are already source-certified at odd depth.
    fixed=[11,17,163,661,733,1489,1861,131,6551,2470991,16782959]
    assert len(fixed)==len(set(fixed))==11
    assert all(p>5 and all(p%k for k in range(2,isqrt(p)+1)) for p in fixed)
    assert coeff(5)==2 and G==8 and w==-8
    assert trace(7)==0 and trace(11)==-4 and trace(13)==2
    out=dict(mod1009_ranks=ranks,hecke_primes_and_traces=[(q,trace(q)) for q in (7,11,13)],
             Manin_cosets=P,primitive_even_vector=J,cusps=sorted(C),cusp_potentials=sorted(t.items()),
             cycle_values=sorted(set(v-t[b]+t[a] for a,b,v in graph)),
             L_over_realpart_period=str(abs(Q(w,G))),absolute_loop_gcd=G,L_symbol=w,
             c5=coeff(5),known_primes_of_twist_M=fixed,
             minimum_v2_coefficient=1+(len(fixed)+1)//2)
    print(json.dumps(out,sort_keys=True,indent=2))
if __name__=='__main__':main()
