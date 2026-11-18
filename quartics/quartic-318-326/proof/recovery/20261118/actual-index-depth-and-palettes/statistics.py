"""Finite checks for the normal-order argument. The asymptotic proof is in the paper."""
from math import isqrt,prod
import json
fs=[(7446,661),(7446,1861),(29784,7445),(476544,119479)]
ds=[3723,3723,7446,-52122]
def sq(x):return x>=0 and isqrt(x)**2==x
def primes(n):return [p for p in range(2,n+1) if all(p%i for i in range(2,isqrt(p)+1))]
def chi(d,p):return {1:1,p-1:-1,0:0}[pow(d%p,(p-1)//2,p)]
def compute():
    for (s,t),d in zip(fs,ds):
        assert (s*(s-4*t))%d==0 and sq(s*(s-4*t)//d) and not sq(d)
    bad=2*3*7*11*17*prod(abs(s*s*(s-4*t)) for s,t in fs)
    for i,(s,t) in enumerate(fs):
        for u,v in fs[:i]:bad*=abs(s*v-t*u)
    checks=0;controls=[]
    for p in primes(1030):
        if bad%p==0:continue
        roots=[a for a in range(p) if not prod(s*a*(a+1)+t for s,t in fs)%p]
        assert len(roots)==4+sum(chi(d,p) for d in ds)
        if p<200:
            for a in roots:
                assert sum(prod(s*(a+j*p)*(a+j*p+1)+t for s,t in fs)%p**2==0 for j in range(p))==1
        checks+=1
        if p<40:controls.append([p,roots])
    return {'distinct_source_discriminants':ds,'good_prime_counts_checked':checks,
       'small_controls':controls,'complement_coefficient_at_examples':{str(t):(4-ds.count(t))/2 for t in [17,409,2449,3723,7446,-52122]}}
if __name__=='__main__':print(json.dumps(compute(),indent=2))
