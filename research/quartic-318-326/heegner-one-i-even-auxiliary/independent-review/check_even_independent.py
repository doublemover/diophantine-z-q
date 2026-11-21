"""Separate exact replay of local descent and Cassels pairing on this one twist."""
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import gcd, isqrt, prod
from pathlib import Path
import hashlib, json, sys

raw = Path(sys.argv[1]).read_bytes()
j = json.loads(raw)
m = 489443591
d = 2811626664334219040035976315
factors = (5,11,17,163,661,733,1489,1861,114649,119851)
aux = (7,13,19,283079)
D = m*d
basis = (-1,2,3,*sorted(factors+aux))
assert d == prod(factors) and m == prod(aux) and d%24==11 and m%24==23 and D%24==13
assert len(set(basis)) == len(basis)
assert all(all(p%u for u in range(2,isqrt(p)+1)) for p in basis[1:])
assert j['d']==d and j['m']==m and j['twist']==-D

@lru_cache
def sqmod(p):
    return {i*i%p for i in range(p)}

assert all(-m%p in sqmod(p) for p in factors)
assert -m%53 not in sqmod(53) and m%53

def vu(x,p):
    x=Q(x)
    assert x
    a,b=x.numerator,x.denominator
    v=0
    while a%p==0:
        a//=p; v+=1
    while b%p==0:
        b//=p; v-=1
    return v,Q(a,b)
def vst(x,p):
    return vu(x,p)[0] if x else 10**9
def red(u,power):
    return u.numerator*pow(u.denominator,-1,power)%power
dyadic = {1:0,3:3,5:2,7:1}
def sc(x,p):
    if p==-1:return int(x<0)
    v,u=vu(x,p)
    return (v%2) | ((dyadic[red(u,8)] if p==2 else int(red(u,p) not in sqmod(p))) << 1)
def width(p):
    return 1 if p==-1 else 3 if p==2 else 2
def res(a,b,p):
    return sc(a,p) | (sc(b,p)<<width(p))
def pairs(p):
    return (res(x,1,p) for x in basis)
def root_trip(x):
    r=[x,x+D,x-3*D]
    if 0 in r:
        i=r.index(0)
        r[i]=prod(z for z in r if z)
    return r
def span(V):
    a={0}
    for k in V: a|={v^k for v in a}
    return a
def dot(a,b):
    return (a&b).bit_count()%2
def rank(rows):
    pivots={}
    for row in rows:
        while row:
            bit=row&(-row)
            if bit not in pivots:
                pivots[bit]=row
                break
            row ^= pivots[bit]
    return len(pivots)

L,R=j['cassels_left'],j['cassels_right']
assert L==[-53761071468515416235,1,-53761071468515416235]
assert R==[30496867310715,1,30496867310715]
retained={v['p']:v['witnesses'] for v in j['local_kummer_rows']}
assert tuple(retained)==basis
rows=[]
for p,W in retained.items():
    w=width(p)
    vectors=[]
    for a,b,_ in W:
        u,v,z=root_trip(Q(a,b))
        assert sc(u*v*z,p)==0
        vectors.append(res(u,v,p))
    local=span(vectors)
    assert len(local) == 2**w
    assert all(res(T[0],T[1],p) in local for T in [L,R,root_trip(0),root_trip(-D)])
    cols=list(pairs(p))
    cols += [c<<w for c in cols]
    for form in range(1,1<<(2*w)):
        if all(not dot(form,u) for u in local):
            rows.append(sum(dot(form,z)<<i for i,z in enumerate(cols)))
def global_sc(a):
    u=abs(a)
    out=int(a<0)
    for i,p in enumerate(basis[1:],1):
        while u%p==0:
            u//=p
            out^=1<<i
    assert u==1
    return out
assert rank(rows)==30 and len(basis)==17
classes=[L,R,root_trip(0),root_trip(-D)]
assert rank([global_sc(a) | (global_sc(b)<<len(basis)) for a,b,_ in classes])==4

def alt_root(u,p,N):
    v,a=vu(u,p)
    assert not v%2 and sc(u,p)==0
    # Keep all four dyadic roots, not the author's single chosen lift.
    if p==2:
        sols={1}
        mod=2
        for _ in range(1,N):
            mod2=2*mod
            un=red(a,mod2)
            sols={r for s in sols for r in (s,s+mod) if (r*r-un)%mod2==0}
            mod=mod2
        r=max(sols)
    else:
        aN=red(a,p**N)
        amodp=aN%p
        r=next(i for i in range(p-1,0,-1) if i*i%p==amodp)
        k=1
        while k<N:
            k2=min(2*k,N)
            mod=p**k2
            r=(r+(aN-r*r)*pow(2*r,-1,mod))%mod
            k=k2
    x=Q(r)*Q(p)**(v//2)
    error=vst(x*x-u,p)
    slope=vst(2*x,p)
    assert error>2*slope
    return x,error-slope

def hilbert_pairs(x,y,p):
    # A character specified by local square-class generators, independently
    # of the valuation formula in the author checker.
    if p==-1:
        return int(x<0 and y<0)
    a,b=sc(x,p),sc(y,p)
    if p==2: # bases [2],[-1],[5]
        rows=(4,2,1) # (2,5) and (-1,-1) only nontrivial entries
    else:    # bases [p], [a nonsquare unit]
        rows=(2|int(p%4==3),1)
    return sum(((a>>i)&1)*dot(r,b) for i,r in enumerate(rows))%2

a=L[0];g=R[0]
A,B,C=j['tangent_seed']
assert a*A*A+D*C*C==B*B and gcd(gcd(A,B),C)==1
neg=[]
for row in j['cassels_rows']:
    p,want=row[:2]
    if len(row)==2:
        assert want==1 and sc(g,p)==0
        continue
    x=Q(*row[4])
    vals=[Q(x-e,t) for e,t in zip([0,-D,3*D],L)]
    approx=[alt_root(v,p,76 if p in (2,3) else 24) for v in vals]
    # Check all eight independent signs in a different residue convention.
    for signs in product((1,-1),repeat=3):
        (z1,s1),(z2,s2),(z3,s3)=[(sg*z,k) for sg,(z,k) in zip(signs,approx)]
        f_1=a*A*z3-B*z2+2*D*C
        f_3=a*A*z1-B*z2+D*C
        assert min(vst(a*A,p)+s3,vst(B,p)+s2)-vst(f_1,p)>=(3 if p==2 else 1)
        assert min(vst(a*A,p)+s1,vst(B,p)+s2)-vst(f_3,p)>=(3 if p==2 else 1)
        got=(-1)**hilbert_pairs(f_1*f_3,g,p)
        assert got==want,(p,signs,got,want)
    if want==-1:neg.append(p)
assert neg==[2,5,733] and len(neg)%2
print('author witness SHA-256:',hashlib.sha256(raw).hexdigest())
print('D =',D)
print('local places, global rank, Selmer dimension:',len(basis),rank(rows),2*len(basis)-rank(rows))
print('negative Cassels places (all eight independent root signs checked):',neg)
