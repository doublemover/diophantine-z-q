#!/usr/bin/env python3
"""Finite arithmetic controls for the exact global first-coordinate sign."""
from pathlib import Path
from math import gcd,isqrt,prod
import json
here=Path(__file__).resolve().parent
payload=json.loads((here/'PINNED-CHARACTER-CONTROLS.json').read_text())

def jacobi(a,n):
    assert n>0 and n%2
    a%=n
    sign=1
    while a:
        while a%2==0:
            a//=2
            if n%8 in (3,5):sign=-sign
        a,n=n,a
        if a%4==n%4==3:sign=-sign
        a%=n
    return sign if n==1 else 0

def isprime(p):
    return p>1 and all(p%d for d in range(2,isqrt(p)+1))

controls=[]
for C in payload['contact_controls']:
    D=C['D'];B=C['A']+3*D*D;d=prod(C['contact_primes'])
    assert gcd(C['A'],D)==gcd(B,d)==1
    assert all(p%408==1 and isprime(p) for p in C['contact_primes'])
    a=jacobi(d,D);z=jacobi(D,d)
    old=prod(C['local_contact_signs'])
    assert a==z==old==C['cassels']==-1
    controls.append(dict(scope='numerical contact profile in recorded phase, not original detector output',
                         epsilon=C['epsilon'],D=D,first=d,new_character=a,old_character=old))

A=17*12**2
D=55
B=A+3*D*D
C=D*D-A
assert gcd(A,D)==1 and isqrt(C)**2!=C and B==3*23*167
assert all(isprime(p) for p in (23,167))
ref=17*B                       # actual first squareclass of T_0
small_B_terms=[jacobi(-2,p) for p in (23,167)]
assert small_B_terms==[-1,-1] and jacobi(ref,D)==1
controls.append(dict(scope='actual rational torsion Kummer, numerical Ready pole',A=A,D=D,C=C,B=B,
                     first=ref,B_local_terms=small_B_terms,
                     denominator_character=jacobi(ref,D),global_character=prod(small_B_terms)))

D=67
B=A+3*D*D
C=D*D-A
assert C==46**2-3*5**2 and gcd(46,5)==1
assert B//3==72**2+11**2 and B%3==0
assert isqrt(C)**2!=C and gcd(A,D)==gcd(B,17)==1
assert jacobi(51,D)==-1
controls.append(dict(scope='exact specified full-lift certificate, numerical Ready not folded',
    A=A,D=D,B=B,C=C,first=51,second=-1,third=-51,C_primitive_norm=[46,5],
    B_over_three_norm=[72,11],global_character=jacobi(51,D)))

beta=payload['actual_scalar']['beta']
R=payload['actual_scalar']['R_input']
assert 3*beta==561*R//4
ps=payload['actual_scalar']['normalizer_primes']
assert all(isprime(p) for p in ps) and prod(ps)==1+114444*R
chi=[jacobi(3*beta,p) for p in ps]
assert chi==[1,-1,-1,1]
assert [jacobi(3,p) for p in (131,6551)]==[1,1]
controls.append(dict(scope='actual scalar conditional key, known denominator part only',
    first=3*beta,known_denominator=prod(ps),known_primes=ps,
    known_characters=chi,known_product=prod(chi),residual_numerator=561,
    result='unknown exceptional denominator and no actual complete lift'))
print(json.dumps(controls,sort_keys=True,indent=2))
