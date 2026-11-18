"""Exact algebra controls; not proof of either sieve or global marked lifting."""
from fractions import Fraction as F
from math import gcd
from collections import Counter
import json

def check():
    count=0
    for i in range(1,32):
        for j in range(i+1,34):
            if gcd(i,j)!=1:continue
            q=F(i,j)
            a=(1-q)*(1+3*q);n=-a*q/(1+2*q)
            for g,y in [(n,a*a/(1+2*q)),(n*q,a*a*(1+q)/(1+2*q))]:
                assert y!=0 and y*y==a*(a-g)*(a+3*g)
            count+=1
    # Good reduction: every projective root forces two characters +.
    tested=0
    for p in (5,7,11,13,19,23,29,31):
        for β in (17,29,41):
            for θ in (409,457,37):
                if β*θ%p==0:continue
                ct=sum((θ*t*t+β*s*s-1)%p==0 and (1+3*θ*t*t)%p==0 for t in range(p) for s in range(p))
                assert ct==(4 if pow((-3*θ)%p,(p-1)//2,p)==pow((3*β)%p,(p-1)//2,p)==1 else 0)
                tested+=1
    assert all((3*i**4+8*i**3-18*i*i-9)%5!=0 for i in range(5))
    return dict(rational_double_checks=count,good_prime_biquadratic_checks=tested,three_division_projective_roots_mod5=0)
if __name__=="__main__": print(json.dumps(check(), indent=2))
