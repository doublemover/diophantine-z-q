#!/usr/bin/env python3
from itertools import product
import json
pairs=set()
for x,y,z in product(range(32),repeat=3):
 if not ((x|y|z)&1):continue
 t=(x*x+6*y*y-2*z*z)%32
 assert t
 v=(t&-t).bit_length()-1
 if v%2==0:
  assert v<=2
  pairs.add((v,(t>>v)%8))
assert pairs=={(0,1),(0,5),(0,7),(2,1),(2,5)}
assert {((x*x-2*z*z)%3) for x,z in product(range(3),repeat=2) if x or z}=={1,2}
assert (3*3-2)%7==0 and (3+3)%7
assert (1+3,2*3)==(4,6)
N=2**16; n=(N-2)//2
assert n==32767
b=(3**n-1)**2-8
assert b>2**103860
print(json.dumps({"primitive_ternary_even_depth_stripped_units_mod8":sorted(pairs),
 "unramified_norm_at3_even_depth":True,
 "odd_ternary_depth3_stripped_unit":2,"bad_7_arm_R_reduction":[4,6],
 "normalized_anchor_exponent":N,"necessary_scalar_translation_depth3":n,
 "strict_bitlength_floor_formula":"(3^32767-1)^2-8",
 "floor_integer_own_binary_length":b.bit_length(),
 "claimed_explicit_weaker_bitlength_floor":"2^103860",
 "prime_search_run":False},indent=2))
