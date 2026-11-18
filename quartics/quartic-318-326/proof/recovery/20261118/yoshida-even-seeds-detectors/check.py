"""CAS-free exact ternary counts, fresh inert-at-two target and genus Laplacian control."""
from math import isqrt,prod,gcd
from itertools import product
import json
def prime(n):return n>1 and all(n%i for i in range(2,isqrt(n)+1))
def r(n,a,b,c):
    h=0
    for z in range(isqrt(n//c)+1):
        for y in range(isqrt((n-c*z*z)//b)+1):
            v=n-c*z*z-b*y*y
            if v%a:continue
            x=isqrt(v//a)
            if a*x*x==v:h+=(1+(x>0))*(1+(y>0))*(1+(z>0))
    return h
def counts(n):return [r(n,1,3,144),r(n,3,9,16)]
def bits(P,k):
    v=[int(pow(k%p,(p-1)//2,p)==p-1) for p in P]
    assert all((pow(p%k,(k-1)//2,k)==k-1)==bool(z) for p,z in zip(P,v));return v
def ker(P):
    L=[[0 if p==q else int(pow(q%p,(p-1)//2,p)==p-1) for q in P] for p in P]
    for i,row in enumerate(L):row[i]=sum(row)%2
    return [v for v in product(range(2),repeat=len(P)) if all(sum(a*b for a,b in zip(r,v))%2==0 for r in L)]
replays=[]
for theta,q in [(409,19),(457,19)]:
    if pow(q,(theta-1)//2,theta)!=theta-1:
        q=next(a for a in range(19,50000,24) if prime(a) and pow(a,8,17)==1 and pow(a,(theta-1)//2,theta)==theta-1)
    P=[q,17,theta];d=prod(P);assert d%24==11 and len(ker(P))==4
    for k in range(13,5000,24):
        if not prime(k) or k in P:continue
        vv=bits(P,k)
        if vv!=[1,1,0]:continue
        one,two=counts(k),counts(k*theta)
        assert one[0]!=one[1] and (one[0]-one[1])%8==4
        if two[0]==two[1]:continue
        assert len(ker(P+[k]))==len(ker(P[:2]+[k]))==2
        assert (-d*k)%24==1
        replays.append(dict(theta=theta,n=q*17,old_P=P,new_k=k,edges=vv,new_D=-d*k,counts_k=one,counts_k_theta=two));break
    else:raise ValueError("No finite double witness")
print(json.dumps(dict(earlier_even={n:counts(n) for n in (73,409,457,29857)},switched=replays),indent=2))
