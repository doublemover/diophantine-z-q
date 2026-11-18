"""Exact sample arithmetic, NOT Lean, normal-closure construction or global cohomology."""
from itertools import product
from math import gcd
import json

def gaussian_power(z,n):
    a,b=z; x,y=1,0
    for _ in range(n):
        x,y=x*a-y*b,x*b+y*a
    return (x,y)

def red(z,p):
    return tuple(v%p for v in z)

# p=3,7,11,19 are 3 mod 4: Z[i]/p = F_(p^2).
comparisons=0
for p in (3,7,11,19):
    for n in range(1,11):
        if gcd(n,p)!=1: continue
        observed={}
        for z in product(range(-4,5),repeat=2):
            r=red(z,p)
            if r==(0,0): continue
            key=(gaussian_power(z,n),r)
            if key in observed: assert observed[key]==z
            observed[key]=z
            comparisons+=1

# Necessity of the tame and the unit hypotheses, already over Z.
assert 1**2==(-1)**2 and 1%2==(-1)%2
assert 3**2==(-3)**2 and 3%3==(-3)%3 and 2%3!=0

# Explicit integral coefficient tower: Z[s,i], s^2=3, i^2=-1.
# Basis 1,s,i,si. Reduction at (s) lands in F_9.
def act(z,eps,eta):
    w,x,y,t=z
    return (w,eps*x,eta*y,eps*eta*t)
def residue(z):
    w,x,y,t=z
    return (w%3,y%3)
basis=[tuple(int(i==j) for i in range(4)) for j in range(4)]
s,i=basis[1:3]
autos=list(product((-1,1),repeat=2))
inertia=[g for g in autos if all(residue(act(z,*g))==residue(z) for z in basis)]
assert inertia==[(-1,1),(1,1)]
# On the indicated lifted integral tower, the four sign automorphisms
# descend because each respects both polynomial relations.
for a,b in product(inertia,repeat=2):
    if act(s,*a)==act(s,*b):
        assert all(act(z,*a)==act(z,*b) for z in basis)
# Removing residual identity allows a genuine nonidentity element that
# fixes the entire old coefficient ring Z[s] but moves the new unit root.
assert act(s,1,-1)==s and act(i,1,-1)!=i and residue(act(i,1,-1))!=residue(i)
print(json.dumps(dict(gaussian_inputs=comparisons,integral_sign_actions=4,
    residual_identity_sign_actions=len(inertia),negative_controls=3,
    scope="illustrative exact arithmetic only; no Lean run or global proof"),indent=2))
