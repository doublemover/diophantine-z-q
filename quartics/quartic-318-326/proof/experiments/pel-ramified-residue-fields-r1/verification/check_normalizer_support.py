#!/usr/bin/env python3
"""Exact checks of emitted certificates; not a replacement for hosted Lean."""
from pathlib import Path
from fractions import Fraction
from itertools import product
from math import gcd,prod
import re,ast,sympy as s
P=Path(__file__).resolve().parent.parent
T=(P/'PELNormalizerQuadraticCertificates318.lean').read_text()
def vectors(text):return [ast.literal_eval('['+v+']') for v in re.findall(r'!\[([^\[\]]+)\]',text)]
C=vectors(T.split('def coefficient',1)[1].split('/--',1)[0]);I=vectors(T.split('def pairIndex',1)[1].split('@[expose]',1)[0])
assert len(C)==10 and all(len(v)==16 for v in C)
assert I==[[0,1,2,3],[1,4,5,6],[2,5,7,8],[3,6,8,9]]
x=s.symbols('a b c d')
def mul(x,y):
 a,b,c,d=x;A,B,C,D=y
 return (a*A-210*b*B-84*b*D+c*C-126*d*B-42*d*D,a*B+b*A-2*b*C+3*c*B+c*D-d*C,a*C+c*A-42*b*D+c*C+42*d*B,a*D+d*A+5*b*C-5*c*B-2*c*D+3*d*C)
def bar(x):a,b,c,d=x;return(a+c,-b,-c,-d)
def norm(x):a,b,c,d=x;return a*a+a*c+210*b*b+210*b*d-c*c+42*d*d
e=[tuple(int(i==j) for i in range(4)) for j in range(4)]
p=[s.expand(v) for y in e for v in mul(mul(x,y),bar(x))]
for i,j in product(range(4),repeat=2):
 assert s.expand(sum(C[I[i][j]][k]*p[k] for k in range(16))-210*x[i]*x[j])==0
assert all(s.expand(v-norm(x)*int(i==0))==0 for i,v in enumerate(mul(x,bar(x))))
z=s.symbols('z0:4')
assert s.expand(210*sum(z[i]*x[i] for i in range(4))**2-sum(z[i]*z[j]*210*x[i]*x[j] for i,j in product(range(4),repeat=2)))==0
# The proof's literal divisor witnesses, not an abstract group count.
w=(P/'PELNormalizerDivisorWords318.lean').read_text().split('all_goals first',1)[1]
V=vectors(w);assert len(V)==16 and len(set(map(tuple,V)))==16
primes=(2,3,5,7);D=[prod(p for p,b in zip(primes,v) if b) for v in V]
assert sorted(D)==[d for d in range(1,211) if 210%d==0]
# Reconstruct emitted original prime norms rather than assuming them.
t=(P/'PELPrimeNormalizerData318.lean').read_text()
A=vectors(t.split('def coefficients',1)[1].split('\n\n',1)[0]);assert len(A)==4
assert [norm(a) for a in A]==list(primes)
# Signed/zero-coordinate denominator and primitive-coordinate sanity.
for nums in product(range(-2,3),repeat=4):
 if not any(nums):continue
 r=[Fraction(a,d) for a,d in zip(nums,(2,3,5,7))];den=prod(v.denominator for v in r)
 a=[int(den*v) for v in r];g=gcd(*a);b=[v//g for v in a]
 assert gcd(*b)==1 and all(r[i]==Fraction(g,den)*b[i] for i in range(4))
# Original norm multiplicativity verifies direction of word division.
y=s.symbols('A B C D')
assert s.expand(norm(mul(x,y))-norm(x)*norm(y))==0
print('PASS: all16 literal quadratic certificates; full signed primitive/denominator checks; exact16 emitted divisor words and original prime norms; original conjugate/norm and Bezout identities. Hosted Lean remains pending.')
