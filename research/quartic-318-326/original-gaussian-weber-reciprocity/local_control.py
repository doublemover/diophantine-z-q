"""Exact small p, non-quartic CI: verify arithmetic Frobenius up to ONE unit."""
from itertools import product

class F:
    def __init__(self,p,d,s):
        self.p,self.d,self.s=p,d,s
        self.pts=list(product(range(p),repeat=d))
        self.zero=self.c(0)
        self.one=self.c(1)
    def c(self,a):return (a%self.p,)+(0,)*(self.d-1)
    def add(self,x,y):return tuple((a+b)%self.p for a,b in zip(x,y))
    def neg(self,x):return tuple(-a%self.p for a in x)
    def sub(self,x,y):return self.add(x,self.neg(y))
    def mul(self,x,y):
        z=[0]*self.d
        for i,a in enumerate(x):
            for j,b in enumerate(y):
                k=i+j
                if k>=self.d:z[k-self.d]+=self.s*a*b
                else:z[k]+=a*b
        return tuple(a%self.p for a in z)
    def pow(self,x,n):
        Y=self.one
        while n:
            if n&1:Y=self.mul(Y,x)
            x=self.mul(x,x); n//=2
        return Y
    def inv(self,x):
        assert x!=self.zero
        return self.pow(x,self.p**self.d-2)
    def div(self,x,y):return self.mul(x,self.inv(y))
    def points(self):
        roots={}
        for y in self.pts:roots.setdefault(self.mul(y,y),[]).append(y)
        yield None
        for x in self.pts:
            rhs=self.sub(self.pow(x,3),x)
            for y in roots.get(rhs,[]):yield (x,y)
    def pneg(self,P):
        if P is None:return None
        return P[0],self.neg(P[1])
    def padd(self,P,Q):
        if P is None:return Q
        if Q is None:return P
        x,y=P; u,v=Q
        if x==u:
            if y==self.neg(v):return None
            assert y==v
            slope=self.div(self.sub(self.mul(self.c(3),self.mul(x,x)),self.one),
                           self.mul(self.c(2),y))
        else:slope=self.div(self.sub(v,y),self.sub(u,x))
        w=self.sub(self.sub(self.mul(slope,slope),x),u)
        return w,self.sub(self.mul(slope,self.sub(x,w)),y)
    def smul(self,n,P):
        if n<0:return self.smul(-n,self.pneg(P))
        Q=None
        while n:
            if n&1:Q=self.padd(P,Q)
            P=self.padd(P,P);n//=2
        return Q
    def rot(self,i,P):
        if P is None:return None
        return self.neg(P[0]),self.mul(i,P[1])
    def frob(self,P,q):
        if P is None:return None
        return self.pow(P[0],q),self.pow(P[1],q)

for p,d in ((5,2),(13,3),(17,2),(29,2),(37,3)):
    s=next(a for a in range(1,p) if pow(a,(p-1)//d,p)!=1)
    f=F(p,d,s)
    pts=list(f.points())
    if p==37:pts=pts[::61]
    for i0 in (i for i in range(p) if (i*i+1)%p==0):
        a,b=next((a,b) for a,b in product(range(-p,p+1),repeat=2)
                 if a*a+b*b==p and (a+b*i0)%p==0)
        i=f.c(i0)
        survivors=set(range(4))
        conjugate_survivors=set(range(4))
        for P in pts:
            T=f.frob(P,p)
            Ts=(T,f.rot(i,T),f.pneg(T),f.pneg(f.rot(i,T)))
            A=f.smul(a,P); B=f.smul(b,f.rot(i,P))
            scaled=f.padd(A,B); conj=f.padd(A,f.pneg(B))
            survivors.intersection_update(j for j,U in enumerate(Ts) if U==scaled)
            conjugate_survivors.intersection_update(j for j,U in enumerate(Ts) if U==conj)
        assert len(survivors)==1
        if d==3:assert not conjugate_survivors
        print("split",p,d,i0,(a,b),len(pts),"global unit",next(iter(survivors)),
              "opposite accepted",bool(conjugate_survivors))

for p in (3,7,11,19,23):
    f=F(p,2,p-1)
    pts=list(f.points())
    assert sum(1 for P in pts if f.frob(P,p)==P)==p+1
    assert all(f.smul(-p,P)==f.frob(P,p*p) for P in pts)
    print("inert",p,"F_p count",p+1,"full F_p² points",len(pts))
