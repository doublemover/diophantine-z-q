#!/usr/bin/env python3
"""Exact P^1(Z/48), Hecke eigensymbol, and fixed-form twist derivative tests."""
from fractions import Fraction as Q
from functools import cache
from math import gcd,lcm,isqrt
import sympy as sp
import json

N=48
p=13
p2=p*p
units=[u for u in range(N) if gcd(u,N)==1]
@cache
def key(c,d):
    c,d=c%N,d%N
    assert gcd(c,d,N)==1
    return min((u*c%N,u*d%N) for u in units)
P=sorted({key(c,d) for c in range(N) for d in range(N) if gcd(c,d,N)==1})
PI={z:i for i,z in enumerate(P)}
assert len(P)==96
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
    # Literal low curve E_{-1}: y^2=x(x+1)(x-3).
    squares={x*x%l:1 if x==0 else 2 for x in range(l)}
    return l-sum(squares.get(x*(x+1)*(x-3)%l,0) for x in range(l))

def eigensymbol():
    rows=[]
    for c,d in P:
        i=idx(c,d)
        # S=(0,-1;1,0) and R=(0,-1;1,-1).
        add(rows,[(i,1),(idx(d,-c),1)])
        add(rows,[(i,1),(idx(d,-c-d),1),(idx(-c-d,c),1)])
        add(rows,[(i,1),(idx(-c,d),1)]) # odd complex-conjugation projection
    dims=[]
    for l in (5,7,11,13,17,19):
        dims.append(len(sp.Matrix(rows).nullspace()))
        e=trace(l)
        for i,z in enumerate(P):
            a,b=rep(*z)
            C=[(i,-e)]
            for x,y in hecke_paths(a,b,l):
                C.extend((j,1) for j in endpoint(y))
                C.extend((j,-1) for j in endpoint(x))
            add(rows,C)
        v=sp.Matrix(rows).nullspace()
        if len(v)==1:
            w=v[0]
            den=lcm(*(int(sp.denom(x)) for x in w))
            J=[int(x*den) for x in w]
            h=gcd(*J)
            if next(x for x in J if x)<0:h=-h
            J=[x//h for x in J]
            assert any(J)
            assert all(sum(a*b for a,b in zip(row,J))==0 for row in rows)
            dims.append(1)
            return J,dims,l
    raise AssertionError(dims)

def exponent(a):
    a%=p2
    assert a%p
    t=pow(a,p-1,p2)
    assert t%p==1
    return ((t-1)//p*pow(p-1,-1,p))%p

def symbol(dvec,a):
    return sum(dvec[i] for i in endpoint(a))

def chi_table(d):
    ch=[int(sp.kronecker_symbol(-d,i)) for i in range(d)]
    assert all(x in (-1,0,1) for x in ch) and ch[1]==1 and ch[d-1]==-1
    return ch

def checks(dvec,d):
    assert d>1 and d%4==3 and gcd(d,6*p)==1 and all(e==1 for e in sp.factorint(d).values())
    M=p2*d;ch=chi_table(d);dinv=pow(d,-1,p2)
    units13=[a for a in range(p2) if a%p]
    assert all(sum(exponent(a) for a in units13 if a%p==t)%p==0 for t in range(1,p))
    group=[0]*p
    for r in range(1,M):
        val=ch[r%d]
        if val and r%p:
            e=exponent(dinv*r)
            group[e]+=val*symbol(dvec,Q(r,M))
    # Separate exact CRT double sum, and degree-one cancellation of stabilization.
    shifted=[0]*p
    tw13=[sum(ch[b]*symbol(dvec,Q(a*d+b*p,p*d)) for b in range(d) if ch[b])
          for a in range(1,p)]
    lower=0
    for a in units13:
        e=exponent(a)
        shifted[e]+=sum(ch[b]*symbol(dvec,Q(a*d+b*p2,M)) for b in range(d) if ch[b])
        lower+=e*tw13[a%p-1]
    assert shifted==group and lower%p==0
    out=sum(i*c for i,c in enumerate(group))%p
    a13=trace(13)*ch[p%d]
    assert a13 in (-2,2)
    return dict(d=d,modulus=M,central_unstabilized=sum(group),group_ring=group,
                derivative_before_unit=out,derivative=out*pow(a13,-2,p)%p,
                lower_stabilization_term_mod13=lower%p,actual_a13=a13)

def main():
    vals,dims,l=eigensymbol()
    rows=[checks(vals,d) for d in (7,11,19,23,35,83,323)]
    assert any(r['central_unstabilized']==0 and r['derivative'] for r in rows)
    assert any(r['central_unstabilized'] for r in rows)
    # Eigenspace selectors, exact Manin basis and synthetic shape all retained.
    print(json.dumps(dict(level=N,cosets=P,primitive_odd_vector=vals,dimensions=dims,final_prime=l,
          controls=rows),sort_keys=True,indent=2))
if __name__=='__main__':main()
