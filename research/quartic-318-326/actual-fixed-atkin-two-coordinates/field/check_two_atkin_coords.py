#!/usr/bin/env python3
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import gcd, prod
import json

ps = (2, 3, 5, 7, 11, 37, 2399)
N = prod(ps)
def factors(signs, primes=ps):
    return [(prod(p for p,i in zip(primes,s) if i),
             prod(w for w,i in zip(signs,s) if i))
            for s in product((0,1), repeat=len(primes))]
@lru_cache(None)
def dedekind(h,k):
    h %= k
    if not h:
        assert k == 1
        return Q(0)
    return -Q(1,4) + (Q(h,k)+Q(k,h)+Q(1,h*k))/12 - dedekind(k,h)
def eta_arg(a,b,c,d): # eta(gamma z)/sqrt(cz+d), angle measured in units pi
    assert a*d-b*c == 1 and c > 0
    return Q(a+d,12*c) - dedekind(d,c) - Q(1,4)
def check(signs):
    M = sum(t*w for t,w in factors(signs))
    assert M == prod(1+p*w for p,w in zip(ps,signs))
    assert sum(w for t,w in factors(signs)) == 0
    assert sum((N//t)*w for t,w in factors(signs)) % 24 == M % 24 == 0
    for p in ps:
        assert sum(w for t,w in factors(signs) if t%p==0)==0
    rows=[]
    for ell,chi in zip(ps[1:],signs[1:]):
        sub=(2,)+tuple(p for p in ps[1:] if p!=ell)
        ws=tuple(w for p,w in zip(ps,signs) if p!=ell)
        P,ts=N//ell,factors(ws,sub)
        a=pow(ell,-1,4*P); b=(ell*a-1)//(4*P)
        S0=sum(w for t,w in ts)
        S1=sum(t*w for t,w in ts)
        SC=sum((4*P//t)*w for t,w in ts)
        assert S0==0 and S1%24==SC%24==0
        A=sum(w*(eta_arg(a,t*b,4*P//t,ell)+chi*eta_arg(ell*a,t*b,4*P//t,1))
              for t,w in ts)
        assert A.denominator==1 and A%2==0
        rows.append(dict(ell=ell,character=chi,a=a,b=b,weighted_t=S1,
                         weighted_c=SC,dedekind_pi_angle=int(A)))
    return dict(characters=list(signs),M=M,eta_q_order=M//24,odd_involutions=rows)
a=check((-1,)*7)
b=check((1,)+(-1,)*6)
m=-a['eta_q_order']
assert N==205042530 and [a['M'],b['M'],m,b['eta_q_order']]==[-41437440,124312320,1726560,5179680]
assert gcd(m,3*m-1)==1
# First coefficients use eta(τ) exponent +1 and every d>1 contributes no q¹.
assert 1 - 3*(-1) == 4
assert 24 - 3*(-24) == 96
print(json.dumps(dict(level=N,first=a,second=b,independent_eta_degrees=[m,3*m],
                      difference_order=3*m-1,width_one_coefficient=4,
                      discriminant_degrees=[24*m,72*m],
                      discriminant_width_one_coefficient=96),indent=2,sort_keys=True))
