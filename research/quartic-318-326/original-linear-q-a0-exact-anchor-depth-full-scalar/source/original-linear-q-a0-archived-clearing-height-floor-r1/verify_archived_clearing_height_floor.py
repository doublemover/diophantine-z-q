#!/usr/bin/env python3
from math import lcm,isqrt,gcd
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json

D=(F(11),F(-6))
def add(A,B):return A[0]+B[0],A[1]+B[1]
def neg(A):return -A[0],-A[1]
def mul(A,B):return A[0]*B[0]+2*A[1]*B[1],A[1]*B[0]+A[0]*B[1]
def norm(A):return A[0]*A[0]-2*A[1]*A[1]
def inv(A):return A[0]/norm(A),-A[1]/norm(A)
def sq(A):return mul(A,A)
def twice(X):
 A=sq(X)
 return mul(sq(add(A,D)),inv(mul((4,0),mul(X,add(A,neg(D))))))
R=(F(1),F(1)); y=(F(0),F(2))
assert sq(y)==mul(R,add(sq(R),neg(D)))
assert 9**2>6**2*2 and 9**2>6**2*2 # 2 < 11±6√2 <20
assert norm(D)==49
assert 441<2**9 and 2**24*7**12<2**60
P=twice(R); P2=twice(P)
assert P==(F(57,8),F(-7,2))
assert P2==(F(8226963211,2285245536),F(-1063929023,1713934152))
A=lcm((2*P2[0]).denominator,norm(P2).denominator)
mn=[A,-A*2*P2[0],A*norm(P2)]
assert all(x==int(x) for x in mn) and gcd(*map(int,mn))==1
assert P2[1] and A==1974452143104 and A>2**40
raw=Path(__file__).with_name("PINNED-ORIGINAL-A0-SCALAR-AND-LABEL-PREFIX.json").read_bytes()
assert sha256(raw).hexdigest()=="5a70adc6e54b42f7d5d289b00a3e0311b7a938e39c489e7a2c3e3781736e2be7"
J=int(json.loads(raw)["J"]); s=1+6**15*3**65536*J; k=2*(s-2)
assert J>0 and J.bit_length()==864 and s.bit_length()==104775 and k>2**104774
assert s>3723 and (s-1)**2>4*s and (s-1)*(s-2)>4 and k>2
print(json.dumps({"D_E_norm":int(norm(D)),"norm_homogeneous_resultant":2**24*7**12,
 "uniform_log2_duplication_error_ceiling":30,"canonical_half_height_error_ceiling":5,
 "primitive_x_2P_minimal_polynomial":list(map(int,mn)),
 "canonical_log2_height_P_strict_lower_bound":"5/4",
 "pinned_J_bitlength":J.bit_length(),"literal_s_bitlength":s.bit_length(),
 "k_strict_lower_bound":"2^104774",
 "literal_unscaled_p_minus_one_binary_logarithm_strict_lower_bound":"2^(2^104774)",
 "actual_Lucas_labels_expanded":False,"prime_search_run":False},indent=2))
