from fractions import Fraction as F
from collections import defaultdict
import json
counts=defaultdict(int)
for n in range(2,19):
 N=n**8;B=n**32;Q=n**56
 assert N>0 and B>=1 and (N+1)**3<=B
 assert F(B*B,N)==Q
 assert F(1,Q+1)<F(N,B*B)
 counts['same_scale_domain_and_order']+=1
 for R in [F(1),F(3,2),F(7,3),F(9)]:
  A=R+1;H=(R*B).__ceil__();J=2*A+1
  assert H<=A*n**32 and 2*H+1<=J*n**32
  for c in [-5,-1,1,2,7]:
   k=abs(c);D=32*k*A*J+1824*k*A+4*J+228
   for ell in [F(0),F(n-1,2),F(n-1)]:
    lg=1+56*ell
    budget=32*F(k*H*(2*H+1),N)+32*k*H*lg+4*(2*H+1)+4*Q*lg
    assert budget<=D*n**58
    counts['expanded_kernel_polynomial']+=1
  counts['canonical_radius']+=1
 # Exact 64th-root instances: A=r^32 implies (A^2)^(1/64)=r.
 for r in [1,2,3]:
  A=r**32;H=A*n**32;root=r*n;assert root**64==H*H
  for divisorC in [F(1),F(3,2),F(7)]:
   moment=(2*H+1)**2*(2*divisorC*root+4)
   E=(2*A+1)**2*(2*divisorC*r+4)
   assert moment<=E*n**65
   counts['exact_fixed_exponent_moments']+=1
 assert n**29*n**65==n**94
 assert F(n**94,B**3)==F(1,n*n)
 counts['normalization_identity']+=1
# Exact exponent audit, not fitted numerics.
assert F(64)*F(1,64)==1
assert 58==2*29 and 29+65==94 and 32*3==96 and 96-94==2
counts['exponent_identity']=5
# Negative controls: excessive fixed divisor loss, wrong denominator
# order, arbitrary-fast diagonal compatibility, and log falsely constant.
assert 29+(64+8)>96 # delta=1/8 is not supported by this envelope
assert F((2**32)**2,2**8)!=2**55
assert 2**(64*64)>64**64 # arbitrary-fast B^(2delta) cannot be absorbed by a fixed N gain
assert 1+56*F(10)>1
counts['negative_controls']=4
print(json.dumps({'status':'PASS','checks':dict(counts),'scope':'Exact rational/integer scaling, polynomial envelope algebra and perfect 64th-root instances. No numerical logarithm approximation, Lean validation, or major/minor common-scale claim.'},indent=2))
