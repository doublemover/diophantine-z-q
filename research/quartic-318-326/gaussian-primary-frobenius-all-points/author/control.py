from math import isqrt
from itertools import product
def prime(p):return p>=2 and all(p%q for q in range(2,isqrt(p)+1))
N=T=G=0
for p in (p for p in range(5,172) if prime(p) and p%4==1):
    def add(P,Q):
        if P is None:return Q
        if Q is None:return P
        x,y=P;z,w=Q
        if x==z and (y+w)%p==0:return None
        n,d=(3*x*x-1,2*y) if x==z else (y-w,x-z)
        lam=n*pow(d%p,-1,p)%p
        v=(lam*lam-x-z)%p
        return (v,(-lam*(v-x)-y)%p)
    def lin(n,P):
        if n<0:return lin(-n,(P[0],-P[1]%p))
        Q=None
        while n:
            if n%2:Q=add(Q,P)
            P=add(P,P)
            n//=2
        return Q
    for i in (i for i in range(p) if (i*i+1)%p==0):
        Q=(i,(1-i)%p);R=(-i%p,(1+i)%p)
        assert (Q[1]*Q[1]-Q[0]**3+Q[0])%p==0
        assert (R[1]*R[1]-R[0]**3+R[0])%p==0
        assert add(Q,Q)==add(R,R)==(0,0)
        assert add((0,0),(0,0)) is None
        N+=1
        S=[Q,(Q[0],-Q[1]%p),R,(R[0],-R[1]%p)]
        assert len(set(S))==4
        T+=4
        for c,d in product(range(-5,6),repeat=2):
            a,b=1-2*(c+d),2*(c-d)
            assert add(lin(a,Q),lin(b,R))==Q
            G+=1
print('literal tangent probes:',N)
print('all four turns distinguished:',T)
print('signed primary coefficient cases:',G)
