#!/usr/bin/env python3
from math import isqrt,prod
import json
prime=131
R=4*661*1861*7445*119479
A=114444*R
beta_primes=[5,11,17,163,661,733,1489,1861]
assert all(all(x%d for d in range(2,isqrt(x)+1)) for x in [prime,*beta_primes])
beta=prod(beta_primes)
assert A==beta//17*(4*3*17)**2
assert A%17==0
N=(1+A)**2-A//17
assert (R,A,1+A)[0]%prime==30 and A%prime==72 and (1+A)%prime==73
assert N%prime**2==93*prime
t=(N//prime)*pow((1+A)**2,-1,prime)%prime
units=[-1,2,3,*beta_primes]
bit=lambda u: int(pow(u%prime,(prime-1)//2,prime)==prime-1)
assert t==82 and bit(t)==1
assert beta%prime==17*17%prime==27
assert [bit(u) for u in units]==[1,1,0,0,0,1,1,1,1,0,0]
print(json.dumps(dict(p=prime,R=R,A=A,N=N,theta_over_p_unit_class=t,beta=beta,
                      legendre_bits=dict(zip(map(str,units),map(bit,units)))),indent=2))
