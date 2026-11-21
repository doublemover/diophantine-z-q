"""Exact fixed-level 180 signed coefficients and auxiliary twist nonvanishing."""
from math import isqrt
from fractions import Fraction as Q
import json

def chi(a,p):
 a%=p
 if a==0:return 0
 return 1 if pow(a,(p-1)//2,p)==1 else -1
def weight(u,y,z):
 b=(10*u+15*y)%23
 if b:return chi(b,23)
 assert z%23==0 and (u-10*y)%23==0
 return chi(y,23)
def c(d):
 n=23*d; signed=representations=0
 for z in range(-isqrt(n//15),isqrt(n//15)+1):
  a=n-15*z*z
  for y in range(-isqrt(a//15),isqrt(a//15)+1):
   a1=a-15*y*y; u=isqrt(a1)
   if not u or u*u!=a1 or (u-z)%2:continue
   representations+=1
   signed+=weight(u,y,z)*chi(u,3)
 return signed,representations
def c_ramified5(d):
 assert d%5==0
 n=23*(d//5); signed=representations=0
 for z in range(-isqrt(n//3),isqrt(n//3)+1):
  a=n-3*z*z
  for y in range(-isqrt(a//3),isqrt(a//3)+1):
   a1=a-3*y*y
   if a1%5:continue
   U=isqrt(a1//5)
   if not U or U*U!=a1//5 or (U-z)%2:continue
   representations+=1
   signed+=weight(5*U,y,z)*(-chi(U,3))
 return signed,representations

# Published Pacetti-Tornaria Table 4 g_{-23} column: all signs match.
T={5:2,8:-4,17:4,53:4,65:-4,77:-8,92:8,113:-4,137:-4,140:8,152:0,173:-12,185:4,188:-8,197:12}
R={d:c(d) for d in T}
assert {d:q[0] for d,q in R.items()}==T
assert all(c_ramified5(d)==q for d,q in R.items() if d%5==0)
old_toy={6953:c(6953),13073:c(13073)}
assert old_toy=={6953:(0,336),13073:(16,408)}

# Independent exact L(f,-23,1)>0 to choose the auxiliary twist in Thm B.
P=300
def ap(p):
 if p in (2,3):return -1
 if p==5:return 1
 return -sum(chi(x*(x+16)*(x+25),p) for x in range(p))
assert tuple(ap(p) for p in (2,3,5,7,11,13,17,19,23,29))==(-1,-1,1,0,-4,-2,2,4,0,-2)
def an(n):
 t=n; out=1
 for p in range(2,isqrt(n)+1):
  if t%p:continue
  k=0
  while t%p==0:
   t//=p;k+=1
  a=ap(p)
  x,y=1,a
  for _ in range(1,k):x,y=y,a*y-(0 if p in (3,5) else p*x)
  out*=y
 if t>1:out*=ap(t)
 return out
# z=2π/sqrt(15*23²) lies between .070 and .071.
# Independently enclose π by Machin's identity and two alternating tails.
def atan_partial(x,k):
 return sum((-1)**n*x**(2*n+1)/Q(2*n+1) for n in range(k))
lpi=16*atan_partial(Q(1,5),6)-4*atan_partial(Q(1,239),5)
upi=16*atan_partial(Q(1,5),5)-4*atan_partial(Q(1,239),6)
assert Q('3.14159')<lpi<upi<Q('3.14160')
assert 89**2<7935<Q('89.1')**2
assert 2*Q('3.14159')/Q('89.1')>Q('.070') and 2*Q('3.14160')/89<Q('.071')
z=Q('.071'); rmin=Q('.931'); rmax=Q('.933')
assert 1-z+z*z/2-z**3/6>rmin
z=Q('.070')
assert 1-z+z*z/2<rmax
L,U=Q(0),Q(0)
r,s=Q(1),Q(1)
for n in range(1,P+1):
 r*=rmin;s*=rmax
 a=Q(2*an(n)*chi(n,23),n)
 L+=min(a*r,a*s);U+=max(a*r,a*s)
# Deligne + d(n) <= n gives |a_n|/n <= n, deliberately coarse.
tail=2*rmax**(P+1)*((P+1)-P*rmax)/(1-rmax)**2
L-=tail;U+=tail
assert Q('.62')<L<U<Q('.712')
assert Q('0.35')*16**2/isqrt(13073)>Q('.78') # coarse independent scale sanity

print(json.dumps(dict(scope="published weighted ternary formula controls and independent auxiliary nonvanishing; no literal d result",
                      published_c_and_positive_u_representations=R,
                      exact_toy_c_and_positive_u_representations=old_toy,
                      auxiliary_minus_23_L1_safe_rational_interval=["31/50","89/125"],
                      level=180,ramified5_reduced_integer_equation="5U^2+3(y^2+z^2)=23d/5",
                      auxiliary_mellin_modes=P),sort_keys=True,indent=2))
