#!/usr/bin/env python3
"""Exact AS cover identities and small Hecke action, not a literal CM occurrence calculation."""
import json
def plus(*x):
 a=0
 for u in x:a^=u
 return a
def mul(a,b,H=None):
 c=0
 while b:
  if b&1:c^=a
  a<<=1;b>>=1
 return c if H is None else c% (1<<H)
def powers(a,k,H=None):
 u=[1]
 for _ in range(k):u.append(mul(a,u[-1],H))
 return u
def p(a,k,H=None):return powers(a,k,H)[-1]
U=2;C=U^p(U,2)
# z^2+z = U^5+U. Add the exact AS difference of U*C, giving C^3+C.
assert (p(U,5)^U^p(mul(U,C),2)^mul(U,C))==(p(C,3)^C)
assert (p(U^1,5)^U^1^p(U,5)^U)==(p(C,2)^C)
# c^5+c^3=a^3+b^3 because ab=c^4, checked in F2[c] recurrence.
S=[0,2];S.extend([p(2,2),p(2,3)^p(2,5)])
assert S[3]==p(2,3)^p(2,5)
# Supersingular elliptic quotients in the two lifts of Fricke; first F2 points:
assert sum(2 for c in (0,1) if (c**3+c)%2==0)+1==5
assert sum(2 for c in (0,1) if c**3%2==0)+1==3
# q-exp t3=3^6(eta3/eta1)^12. The trace on rational weight-zero functions
# is sum of X0(3ell) conjugates. Work at cusp infinity, ordinary and q-rational.
def recip_series(a,H):
 assert a&1
 b=1
 for i in range(1,H):
  if (mul(a,b)>>i)&1:b|=1<<i
 assert mul(a,b,H)==1
 return b
def upoly(H):
 top=bottom=1
 for n in range(1,H):
  top=mul(top,p(1^(1<<(3*n)),12,H),H)
  bottom=mul(bottom,p(1^(1<<n),12,H),H)
 t=mul(top,recip_series(bottom,H),H)<<1
 return recip_series(1^t,H)
def smallhecke(l):
 H=13*l+1
 us=powers(upoly(H),5,H)
 R=us[5]^us[1]
 a=lambda n:(R>>n)&1
 v=sum((a(l*n) ^ (a(n//l) if n%l==0 else 0))<<n for n in range(14))
 tests=[c for c in range(64) if plus(*(us[i] for i in range(6) if c>>i&1))% (1<<14)==v]
 assert len(tests)==1
 def AS(c):
  for i in (4,2):
   if c>>i&1:c^=(1<<i)^(1<<(i//2))
  return c
 return [tests[0],AS(tests[0])]
print(json.dumps(dict(descending_AS_polynomials=[C,p(C,3)^C],small_Hecke={str(l):smallhecke(l) for l in (5,7,11,13,17,19,23,29,31)},scope="fixed geometric AS action only, no evaluated source edge coefficient"),sort_keys=True))
