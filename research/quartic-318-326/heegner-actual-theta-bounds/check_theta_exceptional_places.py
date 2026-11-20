#!/usr/bin/env python3
"""The one extra small bad-reduction prime and exact size arithmetic."""
import json
from math import prod
P=7
def inv(a):
    return pow(a,-1,P)
def add(U,V,d):
    if U is None:return V
    if V is None:return U
    x,y=U;X,Y=V
    if x==X:
        if (y+Y)%P==0:return None
        assert y==Y
        l=(3*x*x-d*d)*inv(2*y)%P
    else:l=(y-Y)*inv(x-X)%P
    w=(l*l-x-X)%P
    ans=(w,(l*(x-w)-y)%P)
    assert (ans[1]**2-ans[0]**3+d*d*ans[0])%P==0
    if d==0: assert ans!=(0,0)    # smooth point on the additive fiber
    return ans
HINDEX=473592745039516333133760
J=15007791093853300881634594756184038091213022964893463173481091096131436857094464566857888173451545095125082924125704203009720761127663357842915750000000
ip=pow(6,15,7)*pow(3,65536,7)*J%7
assert HINDEX%7==ip==4
assert HINDEX%4==0 and 6**15%4==0
cycle={}
for k in (3,4):
    rp=((1+k)%7,2*k%7)
    d=(3-k)%7
    S=None;orbit=[]
    for _ in range(7 if k==3 else 4):
        S=add(S,rp,d)
        orbit.append(S)
    assert orbit[-1] is None and all(t is not None for t in orbit[:-1])
    cycle[k]=orbit
x,y=cycle[3][3]
u1=2*y*inv(x*x)%7; u2=0
# On the smooth branch at O, both actual indexed points are formal.
# The multiplier is a unit and their chart ratio reduces to m=i/h≡1.
NORM=0; f=(u1*u1+u2*u2)*inv(2)%7
R=4376874610839020; A=500907037962860804880; BETA=204618888056724185
n=(1+2*f*inv(R))%7
q=pow(R,-15,7)
w=(n*n+R*q*q)%7
c=12*w*inv(A+1)%7
delta=(1-BETA*c*c)%7
assert (u1,f,n,q,w,c,delta)==(3,1,4,6,5,1,6)
K=prod((131,6551,2470991,16782959))
M0=A+1
assert M0==prod((29,181,1346909,70850399941))
out={'p7':{'orbits':cycle,'delta':delta,'W':w,'c':c},
     'known_theta_product':K,'known_product_mod24':K%24,
     'expanded_H_lower_gt_8_over_9_times':M0*M0,
     'expanded_H_integral_lower':8*M0*M0//9+1,
     'expanded_test_polynomial_min_coefficient':1199923*(8*M0*M0//9+1)}
print(json.dumps(out,indent=2))
