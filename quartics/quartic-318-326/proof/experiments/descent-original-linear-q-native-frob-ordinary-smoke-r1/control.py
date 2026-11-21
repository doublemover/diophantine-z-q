from itertools import product
from random import Random
from fractions import Fraction as Q
from math import prod,isqrt
R=Random(318326)
def norm(x):return x[0]*x[0]+x[1]*x[1]
def un(x):
 a,b=x
 return {(a,b),(-b,a),(-a,-b),(b,-a)}
def prime(n):return n>=2 and all(n%d for d in range(2,isqrt(n)+1))
primed={}
for a,b in product(range(-85,86),repeat=2):
 n=norm((a,b))
 if prime(n):primed.setdefault(n,[]).append((a,b))
orbits=proper=projs=diags=labels=exactref=0
for p,zs in primed.items():
 for w in zs:
  a,b=w
  assert set(zs)==un(w)|un((a,-b))
  for l in (3,5,7,13):
   # Actual translated norms, conjugating a witness does not switch +/-.
   for e in (-1,1):
    assert norm((a+e,b))%l==norm((a+e,-b))%l
  if a%16==9 and b%16==0 and a%7==1 and b%7==3 and a%51==0 and b%51==1:
   assert p%408==1
   exactref+=1
  orbits+=1
M=16*7*51
refa=next(a for a in range(M) if a%16==9 and a%7==1 and a%51==0)
refb=next(b for b in range(M) if b%16==0 and b%7==3 and b%51==1)
for _ in range(512):
 a,b=refa+M*R.randrange(-30,31), refb+M*R.randrange(-30,31)
 assert norm((a,b))%408==1
 assert all(norm((a+e,b))%p for e,p in product((-1,1),(3,7,17)))
 assert (-b)%7!=3
 exactref+=1
for B in range(2,120):
 P={a**e for a in range(B+1) for e in range((B*B).bit_length())}
 for p in range(2,B+1):
  e=2
  while p**e<=B*B:
   assert p**e in P
   proper+=1
   e+=1
for a,b in product(range(1,13),repeat=2):
 # Cyclic quotient C_(ab)->C_a, exact fibre sizes and normalized average.
 for q in range(a):
  F=[z for z in range(a*b) if z%a==q]
  assert len(F)==b
  S=R.sample(range(a*b),R.randrange(a*b+1))
  n=sum(z in S for z in F)
  assert Q(a*n,a*b)==Q(a,a)*Q(n,b)
  projs+=1
for k in range(1,5):
 for t in range(100):
  js=tuple(range(2) for _ in range(k))
  wt={(i,j,u,q):R.randrange(5) for i in range(k) for j in range(2) for u,q in product(range(3),repeat=2)}
  lhs=sum(prod(sum(wt[i,j,u,q] for j in range(2)) for i in range(k)) for u,q in product(range(3),repeat=2))
  rhs=sum(sum(prod(wt[i,types[i],u,q] for i in range(k)) for u,q in product(range(3),repeat=2)) for types in product(*js))
  assert lhs==rhs
  diags+=1
  tag=R.randrange(3)
  assert sum(1 for x in range(2) if x==tag)==(tag<2)
  labels+=1
assert sum((-1)**u for u in range(2))==0
assert sum((-1)**(u+q+((u+q)%2)) for u,q in product(range(2),repeat=2))==4
print(orbits,'prime norm orbit elements;',exactref,'joint signed residue samples;',proper,'proper powers;',projs,'coset means;',diags,'same-key class diagonals;',labels,'tag comparisons, one zero-marginal obstruction')
