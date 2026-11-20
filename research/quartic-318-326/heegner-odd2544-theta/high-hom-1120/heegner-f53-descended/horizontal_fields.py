"""Exact F53^12 and F53^28, with specified k embeddings."""
from dataclasses import dataclass
from types import SimpleNamespace
from functools import lru_cache

p=53
@lru_cache
def field(n,b):
    q=p**n
    def ftrim(w):
        w=[x%p for x in w]
        while len(w)>1 and not w[-1]:w.pop()
        return w
    @dataclass(frozen=True)
    class F:
        v:tuple
        @staticmethod
        def trim(w):return F(tuple(ftrim(w)))
        @staticmethod
        def of(w):return w if isinstance(w,F) else F((w%p,))
        def __bool__(a):return any(a.v)
        def __neg__(a):return F.trim([-x for x in a.v])
        def __add__(a,b):
            b=F.of(b);w=[0]*max(len(a.v),len(b.v))
            for i,x in enumerate(a.v):w[i]+=x
            for i,x in enumerate(b.v):w[i]+=x
            return F.trim(w)
        __radd__=__add__
        def __sub__(a,b):return a+(-F.of(b))
        def __rsub__(a,b):return F.of(b)+(-a)
        def __mul__(a,c):
            c=F.of(c);m=[0]*(len(a.v)+len(c.v)-1)
            for i,x in enumerate(a.v):
                if x:
                    for j,y in enumerate(c.v):
                        if y:m[i+j]+=x*y
            for i in reversed(range(n,len(m))):
                m[i-n+1]-=m[i];m[i-n]-=b*m[i]
            return F.trim(m[:n])
        __rmul__=__mul__
        def __pow__(a,k):
            if k<0:
                assert a
                k%=q-1
            z=one
            while k:
                if k%2:z=z*a
                a=a*a;k//=2
            return z
        def __truediv__(a,b):return a*F.of(b)**-1
        def __rtruediv__(a,b):return F.of(b)*a**-1
        def subfield(a):
            t=a.v[j] if j<len(a.v) else 0
            c=(t*pow(u.v[j],-1,p))%p
            r=a-c*u
            assert len(r.v)==1
            return [r.v[0],c]
    one=F.of(1);zero=F.of(0);w=F((0,1));modulus=[b,1]+[0]*(n-2)+[1]
    def gcd(A,B):
        while B:
            l=pow(B[-1],-1,p)
            A=A[:]
            for i in reversed(range(len(A)-len(B)+1)):
                c=A[i+len(B)-1]*l
                for j,x in enumerate(B):A[i+j]=(A[i+j]-c*x)%p
            A=A[:len(B)-1]
            while A and A[-1]==0:A.pop()
            A,B=B,A
        return A
    assert w**q==w
    for n0 in ([2,3] if n==12 else [2,7]):
        assert len(gcd(modulus,list((w**(p**(n//n0))-w).v)))==1
    for i in range(1,n):
        V=w**i;y=V
        for _ in range(1,n//2):
            V=V**(p*p);y+=V
        x=y-y**p
        if x:
            s=x*x
            assert len(s.v)==1
            a=next(a for a in range(1,p) if a*a*s.v[0]%p==22)
            u=a*x
            break
    else:raise AssertionError("no embedded u")
    assert u*u==F.of(22) and u**p==-u
    j=next(i for i in range(1,len(u.v)) if u.v[i])
    z=next((w+i for i in range(p) if (w+i)**((q-1)//2)==-one),None)
    if z is None:z=next(w*w+i for i in range(p) if (w*w+i)**((q-1)//2)==-one)
    def sqrt(a):
        if not a:return a
        if a**((q-1)//2)!=one:return None
        s=(q-1)&-(q-1);d=(q-1)//s;M=s.bit_length()-1
        c=z**d;b=a**d;r=a**((d+1)//2)
        while b!=one:
            j=1;v=b*b
            while v!=one:v=v*v;j+=1
            assert j<M
            t=c**(1<<(M-j-1))
            r=r*t;c=t*t;b=b*c;M=j
        assert r*r==a
        return r

    @dataclass(frozen=True)
    class E:
        A:F
        B:F
        def contains(self,P):
            return P is None or P[1]**2==P[0]**3+self.A*P[0]+self.B
        def add(self,P,Q):
            if P is None:return Q
            if Q is None:return P
            x,y=P;X,Y=Q
            if x==X and not y+Y:return None
            m=(3*x*x+self.A)/(2*y) if x==X else (Y-y)/(X-x)
            v=m*m-x-X
            return v,m*(x-v)-y
        def mul(self,k,P):
            if k<0:return self.mul(-k,(P[0],-P[1]) if P else None)
            Q=None
            while k:
                if k%2:Q=self.add(P,Q)
                P=self.add(P,P);k//=2
            return Q
    E0=E(zero,one)
    zeta=(-1-u/9)/2
    def omega(P):
        if not P:return None
        x,y=P
        G=(x**p,y**p)
        return E0.add(E0.add(E0.mul(-4,P),E0.mul(-9,(zeta*x,y))),
                      E0.mul(-1,E0.add(G,(zeta*G[0],G[1]))))
    return SimpleNamespace(F=F,E=E,zero=zero,one=one,u=u,omega=omega,E0=E0,
                           modulus=modulus,sqrt=sqrt,n=n,m=p**(n//2)-1)
