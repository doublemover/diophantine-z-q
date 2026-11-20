"""Exact short checks for the denominator-character support reduction."""
import json,math
from pathlib import Path
p=Path(__file__).resolve().parent.parent/'rc-linked-scalar-specialization-r1'
d=json.loads((p/'EXACT-SCALAR-SPECIALIZATION.json').read_text())
R=4376874610839020;A=114444*R;xi1=-3503229612754;xi2=22777399
eta=-2*1861*2027*83761
assert math.isqrt(xi1*xi2//eta)**2==xi1*xi2//eta
def prime(x):
    return x>1 and all(x%j for j in range(2,math.isqrt(x)+1))
def v2(a):
    assert a>0
    return (a&-a).bit_length()-1
h=d['first_passing_h']; j=d['J'];i=6**15*3**65536*j
assert i%h==0
ps=(29,181,1346909,70850399941)
assert math.prod(ps)==A+1 and all(prime(p) and pow(eta%p,(p-1)//2,p)==1 for p in ps)
q=233
assert prime(q) and all(pow(r%q,(q-1)//2,q)==1 for r in (2,-1,7,-R))
assert pow(eta%q,(q-1)//2,q)==q-1
print(json.dumps({'h_v2':v2(h),'shift_v2':v2(i),'shift_over_h_v2':v2(i//h),'Hasse_lower':((2**12)-1)**2,
     'normalizer_prime_factors':ps,'eta_split_each':True,'eta':eta,'finite_character_counterexample':q},indent=2))
