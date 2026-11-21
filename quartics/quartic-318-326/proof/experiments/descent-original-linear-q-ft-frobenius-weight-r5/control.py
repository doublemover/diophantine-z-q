from itertools import product
from math import gcd

def rot(z,m):
    a,b=z
    return ((a%m,b%m),(-b%m,a%m),(-a%m,-b%m),(b%m,-a%m))
def canon(z,m):return min(rot(z,m))
def norm(z,m):return (z[0]**2+z[1]**2)%m
def mul(x,y,m):return ((x[0]*y[0]-x[1]*y[1])%m,(x[0]*y[1]+x[1]*y[0])%m)
def bar(z,m):return z[0]%m,-z[1]%m
def times(a,b,m):
    x,t=a
    y,s=b
    return canon(mul(x,bar(y,m) if t else y,m),m), t^s
def inverse(a,m):
    x,t=a
    N=pow(norm(x,m),-1,m)
    z=(N*x[0],-N*x[1])
    if t:z=bar(z,m)
    return canon(z,m),t
def crt(a,p,b,q):
    return (a+p*((b-a)*pow(p,-1,q)%q))%(p*q)
def shifted(z,j,p):
    return ((z[0]+j)**2+z[1]**2)%p

m=112
A=sorted({canon(z,m) for z in product(range(m),repeat=2) if gcd(norm(z,m),m)==1})
G=list(product(A,(0,1)))
e=(canon((1,0),m),0)
tau=(e[0],1)
assert len(set(G))==2*len(A)
for h in G:assert times(h,inverse(h,m),m)==e
checks=0
for u in A[::max(1,len(A)//54)]:
    predicted={(u,0),(canon(bar(u,m),m),0)}
    actual={times(times(h,(u,0),m),inverse(h,m),m) for h in G}
    assert predicted==actual
    checks+=len(G)
print("index-two normal forms",len(G),"complete sampled conjugacy actions",checks)

cnt=0
for p in (3,5,13):
    M=m*p
    ref=tuple(crt(a,16,b,7) for a,b in zip((9,0),(1,3)))
    positives={}
    pred={}
    for local in product(range(p),repeat=2):
        if not norm(local,p):continue
        z=tuple(crt(a,m,b,p) for a,b in zip(ref,local))
        plus=canon(z,M)
        other=canon(bar(z,M),M)
        assert plus!=other
        assert plus not in positives and other not in positives
        positives[plus]=local
        positives[other]=local
        safe=all(shifted(local,j,p) for j in (-1,1))
        if safe:pred[plus]=pred[other]=local
        for barflag in (False,True):
            for w in rot(bar(z,2*M) if barflag else z,M):
                assert norm(w,2*M)==norm(z,2*M)
                assert (w[0]**2+w[1]**2)% (2*m)==norm(ref,2*m)
                cnt+=1
    exact={}
    for k,local in positives.items():
        for conjugate in (False,True):
            v=bar(k,M) if conjugate else k
            for w in rot(v,M):
                if (w[0]%m,w[1]%m)!=ref:continue
                wlocal=(w[0]%p,w[1]%p)
                if all(shifted(wlocal,j,p) for j in (-1,1)): exact[k]=wlocal
    assert pred==exact
    print("fresh",p,"unique rational classes",len(positives)//2,"retained",len(exact)//2)

p=13
z=tuple(crt(a,m,b,p) for a,b in zip(ref,(0,1)))
w=tuple(crt(a,m,b,p) for a,b in zip(ref,(1,0)))
assert norm(z,2*m*p)==norm(w,2*m*p)
assert all(shifted(z,j,p) for j in (-1,1)) and not shifted(w,-1,p)
print("exact shared cyclotomic norm / opposite safety",z,w,"modulus",2*m*p,"norm",norm(z,2*m*p))
print("signed wide-norm controls",cnt)
