from functools import lru_cache
from itertools import product
from math import gcd, isqrt
def norm(x):return x[0]**2+x[1]**2
def mul(a,b):return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]
def divi(a,b):
    T=mul(a,(b[0],-b[1])); N=norm(b)
    if T[0]%N==0 and T[1]%N==0:return T[0]//N,T[1]//N
def canon(a,n):return min((a[0]%n,a[1]%n),(-a[0]%n,-a[1]%n),(-a[1]%n,a[0]%n),(a[1]%n,-a[0]%n))
@lru_cache(None)
def fs(x):
    N=norm(x)
    if N==1:return (),x
    for a in range(0,isqrt(isqrt(N))+1):
        for b in range(-isqrt(isqrt(N)),isqrt(isqrt(N))+1):
            z=(a,b)
            if 1<norm(z)<=isqrt(N) and (q:=divi(x,z)) is not None:
                s,e=fs(z); t,w=fs(q)
                return s+t,mul(e,w)
    return (x,),(1,0)

for m in (6,12,24,48,120):
    k=0;A=set();F=set()
    for a,b in product(range(m),repeat=2):
        x=(a,b)
        if gcd(norm(x),m)>1:continue
        t,u=fs(x)
        y=u
        for pi in t:
            assert gcd(norm(pi),m)==1 and gcd(norm(pi),6)==1
            y=mul(y,pi)
            F.add(canon(pi,m))
        assert y==x and norm(u)==1
        A.add(canon(x,m))
        k+=1
    print("modulus",m,"unit representatives",k,"classes",len(A),"distinct prime-factor classes visited",len(F))
