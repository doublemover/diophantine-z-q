#!/usr/bin/env python3
from math import prod,gcd
from itertools import product
import json
B=(5,11,17,163,661,733,1489,1861)
beta=prod(B); I=114649; q=119851; P=I*q
def s(x,p):
    c=pow(x%p,(p-1)//2,p)
    return -1 if c==p-1 else c
def cases(L):
    return [prod(x for b,x in zip(row,L) if b) for row in product((0,1),repeat=len(L))]
def atB(m,n,R):
    for p in B:
        if R%p==0:
            if s(-8*P*n,p)!=1:return False
        elif s(8*P*m,p)!=1:return False
    return True
def atP(m,n,D):
    for p in (I,q):
        if D%p==0:
            if min(s(-(P//p)*(m//p),p),s(-(P//p)*(n//p),p))!=1:return False
        elif min(s(m,p),s(n,p))!=1:return False
    return True
def at2(m,n,D):
    for a,b in product(range(16),repeat=2):
        if not (a%2 or b%2):continue
        if D%2==0 and not (a%2 and b%2):continue
        if D%2 and a%2==b%2:continue
        F=a*a-P*b*b; G=a*a-9*P*b*b
        t=2 if D%2==0 else 1
        assert F%t==G%t==0
        if (F//t-m//t)%8==0 and (G//t-n//t)%8==0:return True
    return False
def at3(m,n):
    return s(m,3)==-1 or s(n,3)==1

def main():
    assert P%8==3 and P%3==1 and gcd(beta,6*P)==1
    assert all(s(P,p)==1 for p in B)
    out=[];counts={"candidates":0,"beta":0,"P":0,"2":0,"3":0}
    for e,R,D in product((-1,1),sorted(cases(B)),sorted(cases((2,I,q)))):
        m=e*R*D;n=e*(beta//R)*D
        counts["candidates"]+=1
        if not atB(m,n,R):continue
        counts["beta"]+=1
        if not atP(m,n,D):continue
        counts["P"]+=1
        if not at2(m,n,D):continue
        counts["2"]+=1
        if not at3(m,n):continue
        counts["3"]+=1
        out.append(dict(sign=e,B1=R,D=D,delta1=m,delta2=n))
    print(json.dumps(dict(P=P,beta=beta,counts=counts,everywhere_locally_soluble=out),
          indent=2,sort_keys=True))
if __name__=='__main__':main()
