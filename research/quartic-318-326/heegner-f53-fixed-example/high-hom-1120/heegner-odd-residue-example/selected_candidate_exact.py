#!/usr/bin/env python3
"""Exact arithmetic for the one selected (β,θ)=(17,1) input; no fake π rows."""
import importlib.util,json
from pathlib import Path
from math import gcd,prod,lcm
p=Path(__file__).resolve().parent.parent/"heegner-finite-trace-detector"/"check_same_trace_fd.py"
m=importlib.util.spec_from_file_location("fd",p)
f=importlib.util.module_from_spec(m);m.loader.exec_module(f)

def symbol(a,p):
    b=pow(a%p,(p-1)//2,p)
    return -1 if b==p-1 else b

def ordermod(p,m):
    q=p%m;f=1
    while q!=1:
        q=p*q%m
        f+=1
    return f

def count(p,d,degree):
    a=-sum(symbol(x*(x-d)*(x+3*d),p) for x in range(p))
    u,v=2,a
    for _ in range(2,degree+1):u,v=v,a*v-p*u
    return p**degree+1-v

beta,theta,q0,d=17,1,19,323
assert beta%24==17 and q0%12==7 and symbol(q0,beta)==1 and d==beta*q0 and d%12==11
level,D,p,r=48*d*d,-455,53,13
assert f.squarefree(-D) and D%8==1 and all(symbol(D,q)==1 for q in [3,17,19])
assert symbol(D,p)==-1 and gcd(6*level*D,p)==1
B=60875
assert (B*B-D)%(4*level)==0
classes=sorted(f.class_forms(D))
assert len(classes)==20
torsion_primes=[5,7]
old=[prod(count(t,d,k) for k in [1,2,3,4]) for t in torsion_primes]
assert all(x%r for x in old)
cp=[11,53]
cusp_field=4*d
degrees=[ordermod(t,cusp_field) for t in cp]
C=[count(t,d,k) for t,k in zip(cp,degrees)]
# Cross complements ensure both residue-prime primary parts inject at the other prime.
assert C[0]%cp[1] and C[1]%cp[0]
Cpi=gcd(*C)
assert Cpi==7257600 and Cpi%r
assert count(p,d,1)==52 and count(p,d,2)==2912
E=f.Curve(p,D%p,d)
Q=((9,0),(4,0))
assert E.on_curve(Q) and E.nsmul(r,Q) is None
print(json.dumps({"status":"ARITHMETIC_INPUT_ONLY_NO_REDUCED_CM_OR_PI_ROWS",
                  "beta":beta,"theta":theta,"q0":q0,"d":d,"level":level,
                  "cm_discriminant":D,"orientation_root_mod_4N":B,"lambda":p,
                  "coefficient_prime":r,"residue_quadratic_nonsquare":D%p,
                  "class_count":len(classes),"class_labels":classes,
                  "torsion_primes":torsion_primes,"B_j":old,
                  "cusp_bound_primes":cp,"cusp_residue_degrees":degrees,
                  "C_pi_bound":Cpi,"local_group_counts":[52,2912],
                  "order13_capacity_point_not_a_trace":Q},indent=2))
