#!/usr/bin/env python3
"""Exact eta exponent/cusp arithmetic and the degree-eight sign-trace Gram."""
from fractions import Fraction
from math import gcd, prod
import json

X = {4:1,16:2,24:3,8:-3,12:-1,48:-2}
Y = {8:-2,16:4,24:2,48:-4}
XP = {2:-1,6:3,8:1,24:-3}
x = {d:Y.get(d,0)-2*X.get(d,0) for d in set(Y)|set(X)}
x = {d:r for d,r in x.items() if r}
assert x=={4:-2,8:4,12:2,24:-4}
Ds=[1,2,3,4,6,8,12,16,24,48]
def v(x,p):
    j=0
    while (x%p)==0:
        j+=1;x//=p
    return j
def data(rs):
    order={c:sum(Fraction(48*gcd(c,d)**2*r,24*gcd(c*c,48)*d) for d,r in rs.items())
           for c in Ds}
    assert all(k.denominator==1 for k in order.values())
    return {"eta":rs,"three_Newman_sums":[sum(rs.values()),sum(d*r for d,r in rs.items()),sum(48//d*r for d,r in rs.items())],
            "cusp_order":{p:int(x) for p,x in order.items()},
            "character_constant":str(prod(Fraction(d)**r for d,r in rs.items())),
            "valuation_weights":[sum(v(d,p)*r for d,r in rs.items()) for p in (2,3)]}
rows={"X":data(X),"y48":data(Y),"x":data(x),"x+1":data(XP)}
assert rows["x"]["valuation_weights"]==[0,-2]
assert rows["x+1"]["valuation_weights"]==[-4,0]
assert [(d,h) for d,h in rows["x"]["cusp_order"].items() if h]==[(8,2),(16,2),(24,-2),(48,-2)]
# A bit in mask 4 means the third, imaginary radical sqrt(D/17).
def s(mask):
    return -1 if mask.bit_count()%2 else 1
gram_sign=[[s(j&4)*sum(s(g&(i^j)) for g in range(8)) for j in range(8)] for i in range(8)]
assert all(gram_sign[i][j] == (0 if i!=j else (8 if i<4 else -8))
           for i in range(8) for j in range(8))
# Multiply each last diagonal factor by its negative radical square.
out={"eta":rows,
     "in_basis_1_r_s_rs_t_rt_st_rst_gram_diagonal_over_8":
         ["1","3","17","51","R","3R","17R","51R"],
     "off_diagonal":0,"R":"n/17",
     "v2_conn_etale":{"x":[0,0],"x+1":[0,2],"x-3":[0,2],"hT":[0,0]},
     "v3_conn_etale":{"x":[0,1],"x+1":[0,0],"x-3":[0,1],"hT":[0,0]},
     "U_normalized_v_over_h":{"2":["-1/4","1/4"],"3":["-1/8","1/8"]}}
print(json.dumps(out,sort_keys=True,indent=2))
