from fractions import Fraction as F
from math import gcd
from collections import defaultdict
import json
counts=defaultdict(int)
for p in [0,1,2,5,20]:
 for n in range(2,9):
  N=n**8;B=n**(8*p+32);Q=n**(16*p+56)
  assert F(B*B,N)==Q and (N+1)**3<=B
  counts['same_scale_domain_and_order']+=1
  for R in [F(1),F(3,2),F(7,3)]:
   A=R+1;H=(R*B).__ceil__();J=2*A+1
   assert H<=A*B
   for c in [-3,-1,1,2]:
    D=32*abs(c)*A*J+32*(16*p+57)*abs(c)*A+4*J+4*(16*p+57)
    for ell in [F(0),F(n-1,2),F(n-1)]:
     lg=1+(16*p+56)*ell
     b=32*F(abs(c)*H*(2*H+1),N)+32*abs(c)*H*lg+4*(2*H+1)+4*Q*lg
     assert b<=D*n**(16*p+58)
     counts['flexible_kernel']+=1
  for r in [1,2]:
   A=r**(8*p+32);H=A*B
   assert H**2==(r*n)**(16*p+64)
   for C in [F(1),F(3,2)]:
    moment=(2*H+1)**2*(2*C*r*n+4);E=(2*A+1)**2*(2*C*r+4)
    assert moment<=E*n**(16*p+65)
    counts['fixed_parameter_root_moment']+=1
  assert (8*p+29)+(16*p+65)==24*p+94
  assert F(n**(24*p+94),B**3)==F(1,n*n)
  counts['minor_normalization']+=1
# Actual unit numerators, including modulus one, even and bad moduli.
for N in range(31):
 upper=0
 for q in range(1,N+1):
  units=[a for a in range(q) if gcd(a,q)==1]
  assert len(units)<=q and q**5<=q**6
  upper+=len(units)*q**4
  counts['actual_modulus_unit_root']+=1
 assert upper<=N**6
 counts['literal_mass_completion']+=1
for k in [0,1,2,10,20,100]:
 for n in range(2,10):
  N=n**8;B=n**(8*k+32)
  assert (1+N)**k<=2**k*N**k
  assert F(N**(k+7),B**6)<=F(1,n*n)
  counts['same_parameter_major_normalization']+=1
# Both errors and the main term use literally the same denominator.
for p in range(5):
 for n in range(2,8):
  B=n**(8*p+32);S=F(p+1,3);e=F(1,n*n);m=-F(1,2*n*n)
  major=S*B**3+e*B**3;minor=m*B**3;count=major+minor
  assert count/B**3==S+e+m
  counts['same_scale_major_minor_identity']+=1
assert 8*20+56-192> -2 # fixed p=0 cannot absorb arbitrary k
assert F(16*5+64)*F(1,16*5+64)==1 and F(16*5+64)*F(1,64)!=1
assert len([a for a in range(1) if gcd(a,1)==1])==1
assert 3**(8*2+32)!=3**32 # cannot mix scales in the exact decomposition
counts['negative_controls']=4
print(json.dumps({'status':'PASS','checks':dict(counts),'scope':'Exact integer/rational exponent, actual unit-count and common-scale identity regression; not continuous integration, infinite limit verification or Lean kernel acceptance.'},indent=2))
