"""CAS-free exact reduced form counts and one genus bit, for selected literal supports."""
from itertools import product
from math import prod,isqrt,gcd
import json

def jac(a,n):
    assert n>0 and n%2
    a%=n;v=1
    while a:
        while a%2==0:
            a//=2
            if n%8 in (3,5):v=-v
        if a%4==n%4==3:v=-v
        a,n=n%a,a
    return v if n==1 else 0

def form_count(d):
    h=0
    for a in range(1,isqrt(d//3)+1):
        for b in range(-a,a+1):
            if (b*b+d)%(4*a):continue
            c=(b*b+d)//(4*a)
            if c<a or (b<0 and (a==c or -b==a)) or gcd(a,gcd(b,c))!=1:continue
            h+=1
    return h

def run(ps,bs,tup):
    assert len(set(ps))==len(ps) and all(all(p%k for k in range(2,isqrt(p)+1)) for p in ps)
    d=prod(ps);beta=prod(ps[i] for i in bs);gamma=d//beta
    assert d%12==11 and beta%24==17
    n=len(ps); star=[(-p if p%4==3 else p) for p in ps]
    assert prod(star)==-d
    L=[[0 if i==j else int(jac(q,p)<0) for j,q in enumerate(ps)] for i,p in enumerate(ps)]
    M=[[0 if i==j else int(jac(q,p)<0) for j,q in enumerate(star)] for i,p in enumerate(ps)]
    for X in (L,M):
        for i in range(n):X[i][i]=sum(X[i])%2
    assert M==[list(u) for u in zip(*L)]
    def kernel(X):return [v for v in product(range(2),repeat=n) if all(sum(i*j for i,j in zip(row,v))%2==0 for row in X)]
    B=tuple(int(i in bs) for i in range(n))
    assert len(kernel(L))==len(kernel(M))==4 and B in kernel(L)
    r=next(v for v in kernel(M) if any(v) and not all(v))
    delta=prod(p for p,b in zip(star,r) if b)
    U,V,W=tup
    assert beta*U*U+gamma*V*V==W*W and gcd(U,V)==gcd(W,2*d)==1
    h=form_count(d);m=0;t=h
    while not t%2:m+=1;t//=2
    e=m-(n-2)
    assert e>=2
    sign=jac(delta,W);assert sign in (-1,1) and (sign==1)==(e>=3)
    return dict(d=d,beta=beta,prime_order=ps,K=L,genus=M,dual_bits=r,dual_delta=delta,
        conic=[U,V,W],h=h,cyclic_exponent_e=e,rank4=1,rank8=int(sign==1),sign=sign)

if __name__=='__main__':
 cases=[([19,17],{1},(5,4,27)),([19,17,409],{1},(35,4,381)),
        ([127,17],{1},(23,4,105)),([127,17,409],{1},(19,4,915)),
        ([1087,17],{1},(7,4,135)),([1087,17,409],{1},(1571,4,7005)),
        ([79,11,19,13],{1,2},(1,4,129))]
 ret=[run(*k) for k in cases]
 assert jac(17,1073)==1 and 17*12**2+409*53**2==1073**2
 assert [(r['rank8'],t['rank8']) for r,t in zip(ret[0:6:2],ret[1:6:2])]==[(0,0),(0,0),(1,1)]
 assert ret[-1]['dual_delta'] not in (209,-214643//209)
 print(json.dumps(ret,indent=2))
