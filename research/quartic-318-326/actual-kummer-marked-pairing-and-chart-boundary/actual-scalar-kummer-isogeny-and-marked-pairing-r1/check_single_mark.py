#!/usr/bin/env python3
from math import isqrt,prod,gcd
import json
def prior(p):
    return p>1 and all(p%d for d in range(2,isqrt(p)+1))
def leg(x,p):
    r=pow(x%p,(p-1)//2,p)
    assert r in [1,p-1]
    return 1 if r==1 else -1
def sqfree_class(n):
    out=1
    p=2
    while p*p<=n:
        e=0
        while n%p==0:e^=1;n//=p
        if e:out*=p
        p+=1
    return out*n
beta_act=204618888056724185
old=(5,11,17,163,661,733,1489,1861)
assert all(prior(p) for p in old) and prod(old)==beta_act and beta_act%24==17
old_inert=[p for p in old if leg(-3,p)==-1]
assert old_inert==[5,11,17]
beta=17*409;A=144*beta;D=1007;C=D*D-A
assert gcd(A,D)==1 and 0<A<D*D and sqfree_class(C)!=1
assert all(D%p for p in (2,3,17)) and A%16==A%9==0
# b=17A/D² has stripped unit 1 mod8 at 2, + at3, and + at17.
assert (17*A//16)*pow(D*D,-1,8)%8==1
assert (17*A//9)*pow(D*D,-1,3)%3==1
assert leg(17*A//(17*17)*pow(D*D,-1,17),17)==1
L=D*D+3*A
assert L==5*803549 and prior(803549)
d=beta*L
assert d%24==17 and gcd(beta,L)==1
P=[5,17,409,803549]
cols=[-1,3]+P
rows={p:[leg(d//p if q==p else q,p) for q in cols] for p in P if leg(-3,p)==1}
assert rows=={409:[1]*6}
e=803549
assert leg(-3*beta,e)==1 and leg(3,e)==-1
p2_local_x=sorted({1,(3)%8,(-3)%8,(-9)%8})
assert p2_local_x==[1,3,5,7] and 3*(3-1)*(3+3)==6**2
assert 5*(5*5-4*5+16)%8==1
print(json.dumps(dict(actual_old_beta=beta_act,old_beta_primes=old,
                      retained_inert=old_inert,actual_Selhat_lower=5,actual_Sel2_Eprime_lower=4,
                      standalone=dict(A=A,D=D,C=C,L=L,d=d,signed_columns=cols,split_rows=rows,
                                      admissible_e=e,marked_pairing=-1,contributes_at=e),
                      E1_2_adic_units=p2_local_x,scope='only standalone negative fibre; no actual lambda support claimed'),
                 sort_keys=True,indent=2))
