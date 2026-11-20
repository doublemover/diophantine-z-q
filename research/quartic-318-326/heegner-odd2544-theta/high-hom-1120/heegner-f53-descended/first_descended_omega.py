#!/usr/bin/env python3
"""Lit. first 17-quotient and exact continued Ω x-map on its genuine codomain."""
from dataclasses import dataclass
from random import Random
import json

p=53
q=p**16
D=-455
N=48*323**2
root=30438

@dataclass(frozen=True)
class F:
    v: tuple
    @staticmethod
    def of(x):
        return x if isinstance(x,F) else F((x%p,))
    def __add__(a,b):
        b=F.of(b)
        w=[0]*max(len(a.v),len(b.v))
        for i,x in enumerate(a.v): w[i]+=x
        for i,x in enumerate(b.v): w[i]+=x
        return F.trim(w)
    @staticmethod
    def trim(w):
        w=[x%p for x in w]
        while len(w)>1 and not w[-1]: w.pop()
        return F(tuple(w))
    __radd__=__add__
    def __neg__(a): return F.trim([-x for x in a.v])
    def __sub__(a,b): return a+(-F.of(b))
    def __rsub__(a,b): return F.of(b)+(-a)
    def __mul__(a,b):
        b=F.of(b)
        w=[0]*min(len(a.v)+len(b.v)-1,16)
        for i,x in enumerate(a.v):
            if x:
                for j,y in enumerate(b.v):
                    k=i+j
                    if k<16: w[k]+=x*y
                    else: w[k-16]+=2*x*y
        return F.trim(w)
    __rmul__=__mul__
    def __pow__(a,n):
        if n<0:
            assert a
            if len(a.v)==1: return F.of(pow(a.v[0],n,p))
            n%=q-1
        b=F.of(1)
        while n:
            if n%2: b=b*a
            a=a*a; n//=2
        return b
    def __truediv__(a,b): return a*F.of(b)**-1
    def __rtruediv__(a,b): return F.of(b)*a**-1
    def __bool__(a): return any(a.v)
    def subfield(a):
        assert all(not x or i in [0,8] for i,x in enumerate(a.v)),a
        return [a.v[0],(a.v[8]*pow(8,-1,p))%p if len(a.v)>8 else 0]

one=F.of(1)
zero=F.of(0)
w=F((0,1))
u=8*w**8
assert u*u==F.of(22) and u**p==-u
assert pow(2,26,p)==p-1 and pow(2,4,p)!=1  # binomial irreducibility criterion
assert w**((q-1)//2)==-one
zeta=(-1-u/9)/2
assert zeta*zeta+zeta+1==zero

def sqrt(v):
    if not v: return v
    if v**((q-1)//2)!=one: return None
    s=(q-1)&-(q-1)
    d=(q-1)//s
    M=s.bit_length()-1
    c=w**d; b=v**d; r=v**((d+1)//2)
    while b != one:
        j=1; z=b*b
        while z!=one: z=z*z; j+=1
        assert j<M
        e=c**(1<<(M-j-1))
        r=r*e; c=e*e; b=b*c; M=j
    assert r*r==v
    return r

O=None
@dataclass(frozen=True)
class E:
    A:F
    B:F
    def contains(self,P):
        return P is O or P[1]**2==P[0]**3+self.A*P[0]+self.B
    def add(self,P,Q):
        if P is O:return Q
        if Q is O:return P
        x,y=P; X,Y=Q
        if x==X and y+Y==zero: return O
        if x==X: m=(3*x*x+self.A)/(2*y)
        else: m=(Y-y)/(X-x)
        v=m*m-x-X
        return (v,m*(x-v)-y)
    def mul(self,n,P):
        if n<0: return self.mul(-n,(P[0],-P[1]) if P is not O else O)
        S=O
        while n:
            if n%2: S=self.add(S,P)
            P=self.add(P,P);n//=2
        return S
    def j(self):
        return 1728*4*self.A**3/(4*self.A**3+27*self.B**2)
    def quotient(self,P,l):
        K=[self.mul(i,P) for i in range(1,l)]
        assert self.mul(l,P) is O and O not in K and len(set(K))==l-1
        t=sum((3*x*x+self.A for x,y in K),zero)
        z=sum((5*x**3+3*self.A*x+2*self.B for x,y in K),zero)
        target=E(self.A-5*t,self.B-7*z)
        def f(Q):
            if Q is O or Q in K:return O
            x,y=Q
            for R in K:
                X,Y=self.add(Q,R)
                x+=X-R[0]; y+=Y-R[1]
            T=(x,y)
            assert target.contains(T)
            return T
        return target,f
    def t2(self,P):
        assert P is not O and self.mul(2,P) is O and self.contains(P)
        x=P[0]; a=3*x; b=3*x*x+self.A
        t=256*b/(a*a-4*b)
        assert (t+256)**3/t**2==self.j()
        return t

E0=E(zero,one)
def W(P):
    return (zeta*P[0],P[1]) if P is not O else O
def frob(P):
    return (P[0]**p,P[1]**p) if P is not O else O
def omega(P):
    H=frob(P)
    return E0.add(E0.add(E0.mul(-4,P),E0.mul(-9,W(P))),E0.mul(-1,E0.add(H,W(H))))

def generator(n,l):
    rng=Random(n)
    m=p**8-1   # [-p]^8−1, Frobenius^16−1 on E0.
    for _ in range(100):
        x=F.trim([rng.randrange(p) for _ in range(16)])
        y=sqrt(x**3+1)
        if y is None: continue
        R=E0.mul(m//n,(x,y))
        assert E0.mul(n,R) is O
        T=E0.add(omega(R),E0.mul(root-1,R))
        if E0.mul(n//l,T) is O: continue
        assert E0.mul(n,T) is O
        assert E0.mul(root,T)==omega(T)
        return T
    raise AssertionError("no generator; check field/coefficients")


def coeffk(a,b=0):
    return F.trim([a]+[0]*7+[8*b])

def ptrim(P):
    while P and not P[-1]: P.pop()
    return P
def peval(P,x):
    y=zero
    for a in reversed(P): y=y*x+a
    return y
def padd(P,Q):
    return ptrim([(P[i] if i<len(P) else zero)+(Q[i] if i<len(Q) else zero)
                  for i in range(max(len(P),len(Q)))])
def pneg(P): return [-a for a in P]
def pprod(P,Q):
    if not P or not Q:return []
    Z=[zero]*(len(P)+len(Q)-1)
    for i,a in enumerate(P):
        if a:
            for j,b in enumerate(Q):
                if b:Z[i+j]+=a*b
    return ptrim(Z)
def pdiv(P,Q):
    assert Q
    r=list(P)
    if len(r)<len(Q):return [],r
    d=Q[-1]**-1
    z=[zero]*(len(r)-len(Q)+1)
    for i in reversed(range(len(z))):
        a=r[i+len(Q)-1]*d
        z[i]=a
        if a:
            for j,b in enumerate(Q):r[i+j]-=a*b
    return ptrim(z),ptrim(r)
def pder(P):return ptrim([i*a for i,a in enumerate(P) if i])

def interpolate(pairs,d):
    # Incremental exact Lagrange interpolation.
    V=[]; M=[one]
    for x,y in pairs:
        c=(y-peval(V,x))/peval(M,x)
        V=padd(V,[c*a for a in M])
        M=pprod(M,[-x,one])
    # Rational reconstruction: P == B*Q mod M.
    P=V; Q=[one]; a=M; b=[]
    while len(P)>d+1:
        q,r=pdiv(a,P)
        a,P=P,r
        b,Q=Q,padd(b,pneg(pprod(q,Q)))
    assert P and Q and len(P)<=d+1 and len(Q)<=d+1
    assert all(peval(Q,x) and peval(P,x)==y*peval(Q,x) for x,y in pairs)
    Qinv=Q[-1]**-1
    return [Qinv*t for t in P],[Qinv*t for t in Q]

def coordinates(A,c0):
    # k-level rational points, square roots via brute k table.
    K=[coeffk(a,b) for a in range(p) for b in range(p)]
    if c0 not in K:raise AssertionError
    sq={y*y:y for y in K}
    return [(x,sq[x**3+A.A*x+A.B]) for x in K if x**3+A.A*x+A.B in sq]

def descended_action(A,phi,B,d=114):
    pairs=[]
    labels=set()
    for T in coordinates(A,one):
        X=phi(T); Y=phi(omega(T))
        if X is None or Y is None or X[0] in labels:continue
        pairs.append((X[0],Y[0])); labels.add(X[0])
        if len(pairs)==2*d+1:break
    assert len(pairs)==2*d+1
    num,den=interpolate(pairs,d)
    assert len(num)==115 and len(den)==114
    for s in [num,den]:
        for a in s:a.subfield()
    dn,dd=pder(num),pder(den)
    d_omega=(1+u)/2
    def action(T):
        if T is O:return O
        t,y=T
        N,D=peval(num,t),peval(den,t)
        if not D:return O
        x=N/D
        Y=y*(peval(dn,t)*D-N*peval(dd,t))/(D*D*d_omega)
        U=(x,Y)
        assert B.contains(U)
        return U
    # Exact polynomial identity for the target model plus independent signed
    # checks of the true intertwiner away from the interpolation checks.
    # W = N' D - N D'; yout = y W / (D² d_omega).
    W=padd(pprod(dn,den),pneg(pprod(num,dd)))
    D2=pprod(den,den); D3=pprod(D2,den)
    lhs=pprod(pprod(W,W),[B.B,B.A,zero,one])
    rhs=pprod(den,padd(pprod(pprod(num,num),num),
                         padd([B.A*t for t in pprod(num,D2)],[B.B*t for t in D3])))
    assert lhs==[d_omega*d_omega*t for t in rhs]
    for T in coordinates(A,one)[::61]:
        assert action(phi(T))==phi(omega(T))
    return action,num,den

def any_generator(B,n,l,sample_seed,action,r):
    rng=Random(sample_seed)
    m=p**8-1
    for _ in range(100):
        x=F.trim([rng.randrange(p) for _ in range(16)])
        y=sqrt(x**3+B.A*x+B.B)
        if y is None:continue
        P=B.mul(m//n,(x,y))
        assert B.mul(n,P) is O
        T=B.add(action(P),B.mul(r-1,P))
        if B.mul(n//l,T) is O:continue
        assert B.mul(n,T) is O and B.mul(r,T)==action(T)
        return T
    raise AssertionError('no eigenline generator')

def point_dump(Q):
    return None if Q is O else [list(a.v) for a in Q]

def main():
    G=generator(17,17)
    B,phi=E0.quotient(G,17)
    act,N,D=descended_action(E0,phi,B)
    r=root%17
    f0=any_generator(B,17,17,11,act,r)
    f1=any_generator(B,17,17,37,act,1-r)
    assert f1 not in [B.mul(j,f0) for j in range(17)]
    C,_=B.quotient(B.add(f1,f0),17)
    print(json.dumps({
        'ambient':'F53[w]/(w^16-2), u=8w^8',
        'initial_source_l17_generator':point_dump(G),
        'actual_first_17_quotient':[B.A.subfield(),B.B.subfield()],
        'descended_Omega_x_numerator':[x.subfield() for x in N],
        'descended_Omega_x_denominator':[x.subfield() for x in D],
        'marked_P17': point_dump(f0), 'opposite_Q17':point_dump(f1),
        'actual_mixed_P17_plus_Q17_quotient':[C.A.subfield(),C.B.subfield()],
    },indent=2,sort_keys=True))

if __name__=='__main__':main()
