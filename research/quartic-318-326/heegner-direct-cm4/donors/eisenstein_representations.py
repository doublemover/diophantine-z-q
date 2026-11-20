"""Exact universal ternary representations via an Eisenstein norm sieve.

Unchanged target Q(b,c,d), order HNF, and signed weights are supplied by
the prior q29 documents. No dependence on the bounded C++ box enumerator.
"""
from functools import lru_cache
from math import isqrt, prod

# Z[w], with w^2 + w + 1 = 0
def norm(a):
    x,y=a
    return x*x-x*y+y*y

def mul(a,b):
    x,y=a
    u,v=b
    return x*u-y*v,x*v+y*u-y*v

def conj(a):
    x,y=a
    return x-y,-y

def power(a,e):
    r=(1,0)
    while e:
        if e&1:r=mul(r,a)
        e//=2
        a=mul(a,a)
    return r

def divrem(a,b):
    u,v=mul(a,conj(b)); m=norm(b)
    qb=((2*u+m)//(2*m),(2*v+m)//(2*m))
    s,t=mul(qb,b)
    r=(a[0]-s,a[1]-t)
    assert norm(r)<m
    return r

def sqrtprime(v,p):
    """Return one square root or None, p an odd prime (Tonelli-Shanks)."""
    v%=p
    if v==0:return 0
    if p==2:return v
    if pow(v,(p-1)//2,p)!=1:return None
    if p%4==3:return pow(v,(p+1)//4,p)
    t=p-1
    e=0
    while not t%2:t//=2; e+=1
    z=2
    while pow(z,(p-1)//2,p)!=p-1:z+=1
    c=pow(z,t,p)
    w=pow(v,t,p)
    s=pow(v,(t+1)//2,p)
    while w!=1:
        i=1; h=w*w%p
        while h!=1:i+=1; h=h*h%p
        assert i<e
        a=pow(c,1<<(e-i-1),p)
        s=s*a%p
        c=a*a%p
        w=w*c%p
        e=i
    assert s*s%p==v
    return s

def prime_rep(p):
    assert p%3==1 and p>3
    sr=sqrtprime(-3,p)
    assert sr is not None
    r=(sr-1)*pow(2,-1,p)%p
    assert (r*r+r+1)%p==0
    a,b=(p,0),(-r,1)
    while b!=(0,0):a,b=b,divrem(a,b)
    assert norm(a)==p
    return a

@lru_cache(maxsize=65536)
def split_powers(p,e):
    a=prime_rep(p)
    b=conj(a)
    return tuple(mul(power(a,i),power(b,e-i)) for i in range(e+1))

UNITS=((1,0),(-1,0),(0,1),(0,-1),(1,1),(-1,-1))
def norm_reps(factors):
    fac=(1,0)
    families=[]
    for p,e in factors:
        if p==3:fac=mul(fac,power((1,-1),e))
        elif p%3==2:
            if e%2:return
            fac=mul(fac,(p**(e//2),0))
        else:families.append(split_powers(p,e))
    todo=[fac]
    for S in families:todo=[mul(a,b) for a in todo for b in S]
    for a in todo:
        for unit in UNITS:yield mul(a,unit)

def primes(n):
    T=bytearray(b"\x01")*(n+1)
    T[:2]=b"\x00"*min(2,n+1)
    for p in range(2,isqrt(n)+1):
        if T[p]:T[p*p:n+1:p]=b"\x00"*((n-p*p)//p+1)
    return (p for p in range(2,n+1) if T[p])

def sliced_factors(T):
    """Yield s≥0 and exact factorization of nonnegative (T-s²)/212.

    None is the factorization marker for zero. One sieve per root s mod 212.
    """
    assert T>0
    H=isqrt(T)
    residues=tuple(s for s in range(min(212,H+1)) if (T-s*s)%212==0)
    if not residues:return
    P=tuple(primes(isqrt(T//212)))
    roots=[]
    for p in P:
        if p in (2,53):continue
        r=sqrtprime(T,p)
        if r is None:continue
        roots.append((p,pow(212,-1,p),r))
    for s0 in residues:
        S=range(s0,H+1,212)
        V=[(T-s*s)//212 for s in S]
        F=[[] for _ in V]
        def remove(p,k):
            v=V[k]
            if not v or v%p:return
            e=0
            while v%p==0:v//=p;e+=1
            V[k]=v
            F[k].append((p,e))
        for p in (2,53):
            for k in range(len(V)):remove(p,k)
        for p,inv,r in roots:
            for rp in ((r,-r) if r else (0,)):
                for k in range((rp-s0)*inv%p,len(V),p):remove(p,k)
        for k,s in enumerate(S):
            n=(T-s*s)//212
            if n==0:
                yield s,None
                continue
            if V[k]>1:F[k].append((V[k],1))
            assert prod(p**e for p,e in F[k])==n
            yield s,F[k]

@lru_cache(maxsize=3)
def ambient(den,M):
    """All integer (b,c,d), with no lattice or mark restriction yet."""
    T=3*den*den*M
    out=[]
    for s,fac in sliced_factors(T):
        vals=((0,0),) if fac is None else norm_reps(fac)
        for c,d in vals:
            assert s*s+212*norm((c,d))==T
            z=s-2*c+d
            if z%3: continue
            v=(z//3,c,d)
            out.append(v)
            if s:out.append(tuple(-i for i in v))
    assert len(set(out))==len(out)
    return tuple(out)

def cross(u,v):
    x,y,z=u
    a,b,c=v
    return y*c-z*b,z*a-x*c,x*b-y*a

def dot(u,v):
    return sum(a*b for a,b in zip(u,v))

def order_reps(order,den,M):
    assert tuple(r[0] for r in order)==(den,0,0,0) and den in (1,29)
    a,b,c=([order[i][j] for i in range(1,4)] for j in range(1,4))
    L=(cross(b,c),cross(c,a),cross(a,b))
    det=dot(a,L[0])
    assert det
    for v in ambient(den,M):
        if all(dot(v,h)%det==0 for h in L):
            yield v
