"""F53^18 from w^9=25+12u, u^2=22, ord(25+12u)=27."""
from dataclasses import dataclass
from random import Random
import json

p=53
q=p**18
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
        w=[0]*(len(a.v)+len(b.v)-1)
        for i,x in enumerate(a.v):
            if x:
                for j,y in enumerate(b.v):
                    k=i+j
                    w[k]+=x*y
        for i in reversed(range(18,len(w))):
            w[i-9]+=50*w[i]
            w[i-18]-=w[i]
        return F.trim(w[:18])
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
        assert all(not x or i in [0,9] for i,x in enumerate(a.v)),a
        z=a.v[9] if len(a.v)>9 else 0
        return [(a.v[0]+25*z)%p,12*z%p]

one=F.of(1)
zero=F.of(0)
w=F((0,1))
u=(w**9-25)/12
assert u*u==F.of(22) and u**p==-u
assert (w**9)**27==one and (w**9)**9!=one
assert (1+u)**((q-1)//2)==-one
zeta=(-1-u/9)/2
assert zeta*zeta+zeta+1==zero

def sqrt(v):
    if not v: return v
    if v**((q-1)//2)!=one: return None
    s=(q-1)&-(q-1)
    d=(q-1)//s
    M=s.bit_length()-1
    c=(1+u)**d; b=v**d; r=v**((d+1)//2)
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
    m=p**9+1   # order exponent from Frob^18=[(-p)^9]
    for _ in range(100):
        x=F.trim([rng.randrange(p) for _ in range(18)])
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


