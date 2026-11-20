#!/usr/bin/env python3
"""Arithmetic preflight for a=0/-1 optional 131|theta. No actual theta input."""
from math import gcd,prod
from checked_minimum_scalar_f53_candidates import B,TARGET,isprime,squarefree,leg,local_sign
from minimum_scalar_131_compatibility import classes
import json

A=114444*4376874610839020
assert A%17==0
F=(1+A)**2-A//17

def sf_prime_factors(n):
    L=[]
    p=2
    while p*p<=n:
        if n%p==0:
            n//=p
            assert n%p
            L.append(p)
        p+=1
    if n>1:L.append(n)
    return L

def option(m):
    s=sf_prime_factors(m)
    return {'m':m,'m_prime_support':s,
        'F_mod_prime_support': [F%q for q in s],
        'denominator_root_mod_prime_support': [(1+A)%q for q in s],
        'baseline_prime_symbols': [leg(F,q) for q in s],
        'Jacobi_baseline':prod(leg(F,q) for q in s),
        'baseline_units':gcd(F*(1+A),m)==1,
        'all_eight_beta_and_131_split':all(leg(-m,q)==1 for q in B+(131,)),
        'p53_inert':leg(-m,53)==-1}

def main():
    X=[]
    for m in range(23,2_000_000,24):
        if not (leg(-m,53)==-1 and all(leg(-m,q)==1 for q in B+(131,)) and squarefree(m)):
            continue
        c=option(m);X.append(c)
        if len(X)==3:break
    assert [i['m'] for i in X]==[14231,59399,63839]
    assert X[0]['baseline_units'] and X[0]['baseline_prime_symbols']==[1,-1,1]
    assert X[1]['baseline_units'] and X[1]['baseline_prime_symbols']==[1]
    assert X[2]['baseline_units'] and X[2]['baseline_prime_symbols']==[1]
    m=X[1]['m']; assert isprime(m)
    def new(r,signs,old,pa,pj,lower,upper):
        for p in range(lower+(r-lower)%24,upper,24):
            if local_sign(p,53)!=pa or local_sign(p,131)!=pj:continue
            if local_sign(p,m)!=1:continue
            if not all(local_sign(p,b)==s for b,s in zip(B,signs)):continue
            if not all(leg(p,q)==1 for q in old):continue
            if isprime(p):return p
        raise AssertionError('example search cap reached')
    I=[]
    lo=76177;cap=240_000_000
    for i in range(len(B)-1):
        row=[-1 if j in (i,len(B)-1) else 1 for j in range(len(B))]
        I.append(new(1,row,I,1,1,lo,cap))
        lo=I[-1]+1
    paired=[]
    for bit in [1,-1]:
        q=new(19,[-1]*len(B),I,-1,bit,lo,cap)
        support=B+tuple(I)+(q,)
        assert all(isprime(p) and leg(-m,p)==1 for p in support)
        n=prod(support)
        assert n%24==11 and leg(-n,53)==-1
        paired.append([bit,q,n])
    print(json.dumps({
     'literal_scalar_A':A,'W_equals_one_numerator_F':F,'m_candidates_with_beta_and_131':X,
     'class_numbers':{str(m):len(classes(m)) for m in (14159,14231,59399,63839)},
     'sample_I_for_m_59399_and_131':I,'sample_q0_and_core_for_131_plus_minus':paired,
     'actual_full_theta_factored':False,'companion_nonzero_computed':False,
    },sort_keys=True,indent=2))
if __name__=='__main__':main()
