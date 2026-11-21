import json
from functools import lru_cache

class Field:
    def __init__(self,p,d=None):
        self.p=p
        self.d=d
        self.qq=p if d is None else p*p
    def f(self,a,b=0):
        return (a%self.p)+self.p*(b%self.p)
    def add(self,a,b):
        p=self.p
        return self.f(a%p+b%p,a//p+b//p)
    def neg(self,a):
        return self.f(-(a%self.p),-(a//self.p))
    def sub(self,a,b):
        return self.add(a,self.neg(b))
    def mul(self,a,b):
        p=self.p
        A,B=a%p,a//p
        C,D=b%p,b//p
        return self.f(A*C+(self.d or 0)*B*D,A*D+B*C)
    def conj(self,a):
        return self.f(a%self.p,-(a//self.p))
    def pow(self,a,k):
        v=1
        while k:
            if k%2:
                v=self.mul(v,a)
            a=self.mul(a,a)
            k//=2
        return v
    def inv(self,a):
        if not a: raise ZeroDivisionError()
        return self.pow(a,self.qq-2)
    def div(self,a,b):
        return self.mul(a,self.inv(b))

def control(f):
    O=None
    add,sub,mul,div,pow,n=f.add,f.sub,f.mul,f.div,f.pow,f.f
    def sumf(xs):
        a=0
        for x in xs: a=add(a,x)
        return a
    def epoly(x):
        return mul(x,mul(add(x,1),sub(x,n(3))))
    def rhs(X):
        return sumf([pow(X,8),mul(n(14),pow(X,4)),1])
    def invp(T):
        return O if T is O else (T[0],f.neg(T[1]))
    def plus(P,Q):
        if P is O:return Q
        if Q is O:return P
        x,y=P;X,Y=Q
        if x==X and not add(y,Y):return O
        if x==X:
            assert y==Y
            m=div(sumf([mul(n(3),pow(x,2)),mul(n(-4),x),n(-3)]),mul(n(2),y))
        else:m=div(sub(Y,y),sub(X,x))
        u=sub(sub(add(pow(m,2),n(2)),x),X)
        v=sub(mul(m,sub(x,u)),y)
        assert pow(v,2)==epoly(u)
        return u,v
    def nsm(k,T):
        P=O
        while k:
            if k%2:P=plus(P,T)
            T=plus(T,T)
            k//=2
        return P
    def phi(T):
        X,Y=T
        if X is None or X==0:
            assert Y in (1,n(-1))
            return O if Y==1 else (0,0)
        t=sub(X,f.inv(X));w=div(Y,pow(X,2))
        assert pow(w,2)==sumf([pow(t,4),mul(n(4),pow(t,2)),n(16)])
        x=div(sumf([w,pow(t,2),n(2)]),n(2));y=mul(t,x)
        assert pow(y,2)==epoly(x)
        return x,y
    def w48(T):
        X,Y=T
        if X is None:return 1,mul(n(4),Y)
        if X==1:return None,div(Y,n(4))
        return div(add(X,1),sub(X,1)),div(mul(n(4),Y),pow(sub(X,1),4))
    rt={}
    for x in range(f.qq):rt.setdefault(pow(x,2),[]).append(x)
    ell=[O]+[(x,y) for x in range(f.qq) for y in rt.get(epoly(x),[])]
    hyp=[(None,1),(None,n(-1))]+[(x,y) for x in range(f.qq) for y in rt.get(rhs(x),[])]
    ss=set(hyp)
    for T in hyp:
        U=w48(T)
        assert U in ss and w48(U)==T
        assert phi(U)==plus((n(3),0),invp(phi(T)))
    rr={"elliptic_points":len(ell),"hyp_points_and_w48_checks":len(hyp)}
    if f.d is not None:
        def frob(T):return O if T is O else tuple(f.conj(z) for z in T)
        for i in (1,-1):
            group=[T for T in ell if frob(T)==(T if i==1 else invp(T))]
            rr["frob_plus" if i==1 else "frob_minus"]=len(group)
            rr["four_nonzero_plus" if i==1 else "four_nonzero_minus"]=sum(nsm(4,T) is not O for T in group)
    return rr

report={str(x):control(Field(x)) for x in (5,7,29)}
assert [report[str(p)]["elliptic_points"] for p in (5,7,29)]==[8,8,24]
assert pow(2,14,29)==28
report["29^2"]=control(Field(29,2))
assert (report["29^2"]["frob_plus"],report["29^2"]["frob_minus"])==(24,36)
assert report["29^2"]["four_nonzero_plus"]>0 and report["29^2"]["four_nonzero_minus"]>0

# Exact bound for the analytic route's Frobenius discriminant and ordinary primes.
good=[]
for p in range(5,120):
    if any(p%k==0 for k in range(2,int(p**.5)+1)):continue
    if p%28 not in (5,13,17): continue
    assert pow(-28%p,(p-1)//2,p)==p-1
    good.append(p)
print(json.dumps(dict(scope="fixed modular-model and group controls only; no CM orbit",
                      reductions=report,good_small_p=good),indent=2,sort_keys=True))
