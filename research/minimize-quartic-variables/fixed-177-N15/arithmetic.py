"""Reconstruct the scalar bad set and all decisive constant comparisons using stdlib integers."""
from math import gcd,prod,isqrt
from fractions import Fraction as F
from itertools import combinations
def factors(n):
 n=abs(n);assert n
 p=2;a=set()
 while p*p<=n:
  if n%p==0:
   a.add(p)
   while n%p==0:n//=p
  p=3 if p==2 else p+2
 if n>1:a.add(n)
 return a
S={2,3,5,7,11,13,17,37,41,2399}
forms=[(a,b) for k in (117504,235008) for a,b in [(k,2401),(k,2400),(32*k,77175)]]
gam=S|{149,557}
def ordp(n,p):
 n=abs(n);assert n
 d=0
 while not n%p:n//=p;d+=1
 return d
for a,b in forms:
 gam|=factors(a)|factors(a-b);assert gcd(a*b,149)==1 and min(a,b)>=1
 for p,n in [(2,3),(3,1),(17,1)]:assert ordp(a,p)-ordp(b,p)>=n
for (a,b),(c,d) in combinations(forms,2):gam|=factors(a*d-c*b)
G=prod(gam);c=149**126
assert G==11379293055695063617230310849053151350305581051542357990 and c>2**175*G**4
assert F(74712001,10**6)*2**68*3**16*5**16*7**4<2**149
assert (557-149)%(8*3*17)==0 and F(15*67,8)>125
# ln2<7/10 and ln2>2/3, e^9>2^12 etc via finite exp lower bound:
def lower_exp(n,h):return sum((F(n)**i/prod(range(1,i+1)) for i in range(h+1)),F(0))
assert min(lower_exp(9,22)/7153,lower_exp(14,35)/240000,lower_exp(400,410)/(557*149**52*prod(a+b for a,b in forms)))>1
# |(beta-2401)/k| has chart height cost log max(2402,k) <14.
assert 360*(F(8,2**25)+F(8*14+418,c))+F(2500,c)<F(c,10000)
assert F(1,2**25)+F(14+9,c)<F(1,2)
assert 121*9999**2>120*10000**2 and 484>4*F(12002,100)
assert c>149**66 and 2**100<17*149**30*(557*149**67)**3
print('PASS scalar Γ* (%d primes), unconditional startup valuations for fixed K, small places, exact weight and height budgets.'%len(gam))
