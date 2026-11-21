#!/usr/bin/env python3
from math import gcd,isqrt
import json
A,D,beta,a,u=2448,115,17,12,829
C=D*D-A
B=A+3*D*D
M=B//3
def isprime(p):
    return p>1 and all(p%d for d in range(2,isqrt(p)+1))
assert all(isprime(p) for p in (13,17,19,23,739,829))
assert A==beta*a*a and gcd(A,D)==1 and A<D*D and D%2==1 and gcd(D,51)==1
assert (17*beta)==17**2 and (12*17)**2==17*A
# b is a full rational square, strictly between 0 and 17; exact Ready depths.
def vp(x,p):
    k=0
    while x%p==0: x//=p;k+=1
    return k
assert [vp(17*A,p) for p in (2,3,17)]==[4,2,2]
assert C==13*829==110**2-3*21**2 and gcd(110,21)==1
assert B==3*M and M==19*739 and 19%4==739%4==3
assert u%8==5 and u%3==1 and pow(u%17,8,17)==1
assert (2136**2+u)%M==0
assert 597**2+u*20**2==M*7**2
assert D==5*23 and pow(51%5,2,5)==1 and pow(51%23,11,23)==22
print(json.dumps(dict(scope='numerical Ready pole, not original folded source',A=A,D=D,C=C,M=M,
    specified_gaussian_lift=False,alternative_u=u,finite_root=2136,relative_norm=[597,20,7],
    first=51,second=-u,third=-51*u,cas_sign=-1),indent=2,sort_keys=True))
