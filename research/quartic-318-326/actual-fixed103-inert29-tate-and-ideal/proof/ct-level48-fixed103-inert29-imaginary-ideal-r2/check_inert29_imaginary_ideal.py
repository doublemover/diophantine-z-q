#!/usr/bin/env python3
from pathlib import Path
from hashlib import sha256
import json
p=Path(__file__).resolve().parent.parent/'ct-level48-fixed103-inert29-tate-cubic-r1'
assert sha256((p/'SHA256SUMS').read_bytes()).hexdigest()=='c5a2659758dcb4dc72e846e8e855ffffa253e086068ee580d57a2ecf5629369e'
f=[27,99,63,16]
assert all(sum(c*x**j for j,c in enumerate(f))%23 for x in range(23))
def v2(n):return (n&-n).bit_length()-1
assert list(map(v2,f))==[0,0,0,4]
p=29
def mu(u,v):
 a,b=u;c,d=v;return ((a*c+2*b*d)%p,(a*d+b*c)%p)
def pw(u,i):
 z=(1,0)
 while i:
  if i&1:z=mu(u,z)
  i//=2;u=mu(u,u)
 return z
g=(14,5)
assert pw(g,3)==(1,0) and g!=(1,0) and pw(g,29)==pw(g,2)
assert (280*(1-29)-560)%840==0
D=-1751*241
assert D%29==17 and (2*9**2-D)%29==0
# Synthetic norm-one elements in this actual reference field. The two residues
# prove that norm/absolute-ideal size alone cannot certify the cube test.
B=(9,)
A=[]
for a in range(1,29):
 z=mu((a,9),pw((a,-9%29),839))
 w=pw(z,280)
 if not any(t[-1]==w for t in A):A.append((a,z,w))
assert len(A)==3
print(json.dumps(dict(scope='field/ideal criterion; synthetic norm-one controls do not recover CM norm ideal',
 irreducibility_prime=23,rational_function_x_cubic=f,newton_v2=list(map(v2,f)),
 known_reference_cubic=g,reference_imaginary_field_D=D,synthetic_norm_one_residues=A),
 sort_keys=True,separators=(',',':')))
