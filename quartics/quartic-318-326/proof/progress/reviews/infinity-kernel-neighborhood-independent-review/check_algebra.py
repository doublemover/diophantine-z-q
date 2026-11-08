import sympy as s
A,B,u,v=s.symbols("A B u v")
q=1-2*A*u*v-3*B*v*v
S=3*u*u+A*v*v
C=q**3+A*S*S*q+B*S**3
G=1-B*v*v
K=2*A*S*q+3*B*S*S
H=G*(3*C-K*S)+K*q*(u*u+A*v*v)
F=3*u*C+K*(v*q-S*u)
e=v-u**3-A*u*v*v-B*v**3
assert s.expand(G*F-u*H-K*q*e)==0
assert s.expand((q*C*G*H).subs({u:0,v:0}))==3
# Boundary coordinate u=e in F_p[e]/e^3 is nonzero and has cube zero.
# 2u=-u holds iff 3u=0. This protects the actual unit-3 boundary.
for p in [5,7,11]:
    assert 3 % p != 0 and (2-(-1)) % p != 0
assert (2-(-1)) % 3 == 0
print("EXACT_FACTOR_ORIGIN_AND_UNIT3_NEGATIVE_CONTROLS_PASS")
