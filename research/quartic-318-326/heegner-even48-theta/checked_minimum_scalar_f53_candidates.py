#!/usr/bin/env python3
"""Bounded arithmetic only: fixed a=0/-1 scalar beta, permitted fresh core."""
from math import isqrt,prod
from functools import lru_cache
import json

B=(5,11,17,163,661,733,1489,1861)
TARGET=204618888056724185
P=53
def isprime(n):
    return n>=2 and all(n%r for r in range(2,isqrt(n)+1))
def squarefree(n):
    return n>0 and all(n%(r*r) for r in range(2,isqrt(n)+1))
def leg(a,p):
    pa=pow(a%p,(p-1)//2,p)
    assert pa in [0,1,p-1]
    return -1 if pa==p-1 else pa
@lru_cache
def sqres(p):
    return frozenset(pow(i,2,p) for i in range(1,(p+1)//2))
def local_sign(a,p):
    u=a%p
    return 1 if u in sqres(p) else (-1 if u else 0)
def findm(count,limit):
    out=[]
    for m in range(23,limit,24):
        if local_sign(-m,P)!=-1:continue
        if all(local_sign(-m,q)==1 for q in B) and squarefree(m):
            out.append(m)
            if len(out)==count:return out
    raise AssertionError('bound too small')
def findp(residue,m,beta_signs,before,p53_sign,lower,upper):
    for p in range(lower+(residue-lower)%24,upper,24):
        if local_sign(p,P)!=p53_sign:continue
        if local_sign(p,m)!=1:continue
        if not all(local_sign(p,b)==s for b,s in zip(B,beta_signs)):continue
        if not all(leg(p,q)==1 for q in before):continue
        if isprime(p):
            assert leg(-m,p)==1 # independent of QR filter used to find p
            return p
    raise AssertionError('bounded candidate search exhausted')
def main():
    assert all(isprime(q) for q in B)
    assert prod(B)==TARGET and TARGET%24==17
    assert leg(TARGET,P)==1
    ms=findm(8,2_000_000)
    m=ms[0]
    assert m==14159 and isprime(m)
    lower,upper=76177,160_000_000
    I=[]
    for i in range(len(B)-1):
        s=[-1 if j in (i,len(B)-1) else 1 for j in range(len(B))]
        I.append(findp(1,m,s,I,1,lower,upper))
        lower=I[-1]+1
    q0=findp(19,m,[-1]*len(B),I,-1,lower,upper)
    n=TARGET*prod(I)*q0
    assert n%24==11 and leg(-n,P)==-1
    assert len(set(B+tuple(I)+(q0,)))==16
    assert all(isprime(q) and leg(-m,q)==1 for q in B+tuple(I)+(q0,))
    assert all(p%12==1 for p in I) and q0%12==7
    assert all(leg(b,i)==leg(i,b) for b in B for i in I)
    for k,i in enumerate(I):
        assert all(leg(i,b)==(-1 if j in (k,len(B)-1) else 1)
                   for j,b in enumerate(B))
    assert all(leg(q0,q)==1 for q in I) and all(leg(q0,b)==-1 for b in B)
    assert all(leg(i,j)==1 for i in I for j in I if i!=j)
    print(json.dumps({
        'status':'literal minimum scalar beta only; core CRT example, theta and actual linked h/labeled pole not chosen',
        'beta':TARGET,'ordered_beta_primes':B,'h_star_candidate':-m,
        'first_eight_m_for_these_beta_primes':ms,
        'p53_inert':leg(-m,P)==-1,'beta_legendre_p53':leg(TARGET,P),
        'auxiliary_I':I,'auxiliary_q0':q0,'input_new_prime_threshold':76176,'search_cap':upper,
        'n_core_example':n,'n_core_decimal_digits':len(str(n)),
        'raw_unit_branches_before_class_count':prod(q-1 for q in B+tuple(I)+(q0,)),
        'prime_to_53_and_core_detector_sign':leg(-n,P),
        'same_K_split_all_core':True,
        'companion_nonvanishing_proved':False,
        'actual_theta_supplied':False,
    },indent=2,sort_keys=True))
if __name__=='__main__':main()
