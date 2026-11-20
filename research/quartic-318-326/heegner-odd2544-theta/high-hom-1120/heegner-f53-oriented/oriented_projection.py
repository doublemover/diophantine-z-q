#!/usr/bin/env python3
"""One literal marked CM reduction and its actual X0(48) projection.

Uses only Python's stdlib, exact finite fields and short Weierstrass addition.
The level N kernel itself is specified by the exact endomorphism eigenline,
not determined from j-invariants.
"""
from dataclasses import dataclass
from random import Random
import json

p=53
q=p**8
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
        w=[0]*min(len(a.v)+len(b.v)-1,8)
        for i,x in enumerate(a.v):
            if x:
                for j,y in enumerate(b.v):
                    k=i+j
                    if k<8: w[k]+=x*y
                    else: w[k-8]+=2*x*y
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
        assert all(not x or i in [0,4] for i,x in enumerate(a.v)),a
        return [a.v[0],(a.v[4]*pow(8,-1,p))%p if len(a.v)>4 else 0]

one=F.of(1)
zero=F.of(0)
w=F((0,1))
u=8*w**4
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
    m=p**4-1   # [-p]^4−1, Frobenius^8−1 on E0.
    for _ in range(100):
        x=F.trim([rng.randrange(p) for _ in range(8)])
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

def edges(E,P,n):
    out=[]
    for _ in range(n):
        R=E.mul(2**(n-1),P)
        t=E.t2(R)
        U,f=E.quotient(R,2)
        assert (t+16)**3/t==U.j()
        out.append(t)
        E,P,n=U,f(P),n-1
    return out

k=[F.trim([a,0,0,0,8*b]) for a in range(p) for b in range(p)]
def haupt(edges):
    row=edges
    for c,bump in [(16,16),(4,8),(2,4)]:
        nxt=[]
        for a,b in zip(row,row[1:]):
            candidates=[x for x in k if x+c and x**2==a*(x+c) and x*(x+bump)==b]
            assert len(candidates)==1,(c,a,b,candidates)
            nxt.extend(candidates)
        row=nxt
    assert len(row)==1
    return row[0]

def chart(T,U):
    found=[]
    for x in k:
        if not x: continue
        y=(U+2)*x+1
        if y and y*y-y*(x**4+1)==3*x**4 and (x-2)*y+3*x==T*y:
            found.append((x,y))
    assert len(found)==1,found
    return found[0]

def point_dump(Q):
    return None if Q is O else [list(z.v) for z in Q]

def main():
    assert (root*root-root+114)%N==0
    g16,g3=generator(16,2),generator(3,3)
    E3,f3=E0.quotient(g3,3)
    a,b=edges(E0,g16,4),edges(E3,f3(g16),4)
    T,U=haupt(a),haupt(b)
    x,y=chart(T,U)
    C=2*y-(x**4+1)
    r=(x-1/x)/2; s=C/(4*x*x)
    assert s*s==r**4+r*r+1
    assert r
    A=(s+1)/(r*r); B=(A*A-1)*r
    assert B*B==(A*A-1)*(2*A+1)
    X,Y=2*A+1,2*B
    assert Y*Y==X*(X+1)*(X-3)
    # Translate the Weierstrass x by x=w0+2/3 to use short addition.
    target=E(-F.of(13)/3,-F.of(70)/27)
    R=target.add((X-F.of(2)/3,Y),(F.of(3)-F.of(2)/3,zero))
    assert R is not O and target.contains(R)
    based=(R[0]+F.of(2)/3,R[1])
    assert based[1]**2==based[0]*(based[0]+1)*(based[0]-3)
    print(json.dumps(dict(level=N,field="F53[u]/(u²−22)",ambient="w^8=2,u=8w^4",
             g16=point_dump(g16),g3=point_dump(g3),E3=[E3.A.subfield(),E3.B.subfield()],
             t2_untouched=[z.subfield() for z in a],t2_after3=[z.subfield() for z in b],
             t16=[T.subfield(),U.subfield()],x48=x.subfield(),y48=y.subfield(),
             phi_raw=[X.subfield(),Y.subfield()],phi_based=[z.subfield() for z in based]),indent=2,sort_keys=True))

if __name__=="__main__":main()
