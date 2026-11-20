#!/usr/bin/env python3
"""One extra actual-support split guard; 131 is not substituted for theta."""
from math import isqrt,prod,gcd
from checked_minimum_scalar_f53_candidates import B,TARGET,P,isprime,squarefree,leg,local_sign
import json

def classes(m):
    R=[]
    for a in range(1,isqrt(m//3)+1):
        for b in range(-a,a+1):
            c,f=divmod(b*b+m,4*a)
            if f or c<a or gcd(gcd(a,b),c)!=1:continue
            if (abs(b)==a or a==c) and b<0:continue
            R.append((a,b,c))
    return R

def main():
    qJ=131
    assert isprime(qJ)
    m=next(m for m in range(23,100_000,24)
           if local_sign(-m,53)==-1 and squarefree(m)
           and all(local_sign(-m,q)==1 for q in B+(qJ,)))
    assert m==14231 and m==7*19*107 and all(isprime(q) for q in (7,19,107))
    assert leg(-14159,qJ)==-1 and leg(-m,qJ)==1
    assert [len(classes(n)) for n in (14159,m)]==[173,164]
    def new(r,signs,old,pa,pj,lower,upper):
        for p in range(lower+(r-lower)%24,upper,24):
            if local_sign(p,53)!=pa or local_sign(p,131)!=pj:continue
            if prod(local_sign(p,q) for q in (7,19,107))!=1:continue
            if not all(local_sign(p,b)==s for b,s in zip(B,signs)):continue
            if not all(leg(p,q)==1 for q in old):continue
            if isprime(p):
                assert leg(-m,p)==1
                return p
        raise AssertionError('finite search cap reached')
    I=[]
    lo=76177;cap=240_000_000
    for i in range(len(B)-1):
        row=[-1 if j in (i,len(B)-1) else 1 for j in range(len(B))]
        I.append(new(1,row,I,1,1,lo,cap))
        assert prod(leg(b,I[-1]) for b in B)==1
        lo=I[-1]+1
    qs=[]
    for j in [1,-1]:
        q=new(19,[-1]*len(B),I,-1,j,lo,cap)
        qs.append(q)
    C=[TARGET*prod(I)*q for q in qs]
    for q,n in zip(qs,C):
        assert len(set(B+tuple(I)+(q,)))==16 and n%24==11
        assert leg(-n,53)==-1 and all(leg(-m,t)==1 for t in B+tuple(I)+(q,))
        assert all(leg(q,t)==1 for t in I)
    print(json.dumps({
        'status':'bounded core-only examples with one extra split prime; not the original complete theta or chosen h',
        'beta':TARGET, 'm_min_first_eight_support_plus_131':m,
        'class_numbers':{'14159':len(classes(14159)),'14231':len(classes(m))},
        '131_splits_in_m_14159':False,'131_splits_in_m_14231':True,
        'I':I,'q0_for_131_symbol_plus_minus':qs,'n_core_for_131_plus_minus':C,
        'both_core_examples_same_p53_and_d_local_type':True,
        'full_theta_supplied':False, 'companion_central_value_computed':False,
    },sort_keys=True,indent=2))
if __name__=='__main__':main()
