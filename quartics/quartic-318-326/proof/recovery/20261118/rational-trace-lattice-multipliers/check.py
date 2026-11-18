from math import isqrt
import json
def prime(p):return p>1 and all(p%q for q in range(2,isqrt(p)+1))
def r(n,a,b,c):
    h=0
    for z in range(isqrt(n//c)+1):
        for y in range(isqrt((n-c*z*z)//b)+1):
            v=n-c*z*z-b*y*y
            if v%a:continue
            x=isqrt(v//a)
            if a*x*x==v:h+=(1+(x>0))*(1+(y>0))*(1+(z>0))
    return h
def C(n):return r(n,1,3,144)-r(n,3,9,16)-(1 if n==1 else 0)
rows={n:C(n) for n in [1,13,73,109,409,457,73*409,109*409]}
assert list(rows.values())==[1,4,-8,-4,0,-16,-16,16]
primes=[p for p in range(5,11000) if prime(p) and p%24 in (1,13)]
assert all(C(p)%8==(4 if p%24==13 else 0) for p in primes)
print(json.dumps(dict(coefficients=rows,prime_congruences_checked=len(primes),low_grade_forced_elsewhere=(rows[73]%8==rows[73*409]%8==0),switched_relative=[abs(rows[109]//rows[13]),abs(rows[109*409]//rows[13])]),indent=2))
