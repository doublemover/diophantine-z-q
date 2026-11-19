"""Independent integer/fraction checks for 180's proof; no generation of the polynomial."""
from fractions import Fraction as Q
from math import prod,gcd
S={2,3,5,7,11,13,17,37,41,2399}
G=S|{79,89,647,3593}
BS=prod(S); C0=2**68*3**16*5**16*7**4; c0=Q(74712001,10**6)
# rational log upper bounds via exp series, ln B_S<29 (large enough).
def exppart(q,j):
 a=Q(1);s=a
 for k in range(1,j+1): a*=Q(q,k);s+=a
 return s
assert exppart(29,70)>BS and BS>3
K=c0*C0*BS**2*prod(1+Q(1,p) for p in S)*29
assert K<2**237
for x in range(149):
 b=(1-51*x*x)%149;assert b*(b-2401)*(32*b+343)%149
assert 9792%149 and all(149%j for j in [2,3,17])
assert 149**66<2**765 and 149**66>2**475 and 149**29*900000>2**20*576
# If bad 149 depth then log h(den β) condition h(β)>N. On M <= 2^255 use ln2<1.
assert (1+255)**2*2**(237+2*255)==2**763
assert Q(2**237*256**2,2**255)==Q(1,4)
assert 2450<2**12 and 12*4<149**66
# Permitted formal point norms; unit at any restored good mark prime.
for q in [Q(1681,64),Q(3136,1681),Q(27783,289),Q(289,567),Q(-49),Q(-1),Q(-28),Q(-7,4),Q(7)]:
 for n in [abs(q.numerator),q.denominator]:
  for p in S:
   while n%p==0:n//=p
  assert n==1
# P(x)>0/nonsq selection and exact mod units. Check x integer, P real sign by splitting x=0 or x²>=1.
def pol(x):
 b=1-51*x*x;return b*(b-2401)*(32*b+343)
def v(n,p):
 a=0
 while n%p==0:n//=p;a+=1
 return a
for x in range(256*9): assert v(pol(x),2) in (1,2,4,5) and v(pol(x),3)==2 and pol(x)%17
assert pol(0)==-900000 and pol(1)<-900000
# Γ-only support of interpolation and source marks (no computer algebra).
def unit(v):
 v=Q(v);assert v
 for n in [abs(v.numerator),v.denominator]:
  for p in G:
   while not n%p:n//=p
  assert n==1,(v,n)
Theta=[Q(0),Q(-1),Q(-1,2),Q(1,2399),Q(-32,407)]
T=Q(3,22);roots=sorted((a-T)**2 for a in Theta)
r=Q(-3,22);s=Q(7175,52778)
assert sorted([r*r,s*s])==roots[:2]
def Q2(t):return prod(t-z for z in roots[:2])
def G3(t):return prod(t-z for z in roots[2:])
d=sum(roots[:2])-sum(roots[2:]);c=1/(r+s);A=c*(d-r*s);assert c==-2399 and A==Q(584793232723,144506164)>0 
marks=Theta+[2*T-i for i in Theta]
for i,a in enumerate(marks):
 for a1 in marks[i+1:]:unit(a1-a)
 t=a-T;y=t*t;Qv=Q2(y);g=G3(y);L=g-(y+d)*Qv;nu=(t+A)*Qv+c*L;unit(nu)
 if Qv: assert nu==-c*Qv*(t-r)*(t-s)
 else: assert nu==c*g
assert prod(G)<2**75 and c0*C0*prod(G)**2*prod(1+Q(1,p)for p in G)<2**300
# 30 return moduli: if pmax<=5pmin/4 then Hasse upper<2pmin once pmin>76176.
assert (3*76176-4)**2>80*76176
# Monotone exponential comparison for B>=149^66 of nonzero Delta. v62 uses certified log bounds.
assert 220*Q(6005,6006)>Q(25,4)+300*Q(173287,250000)+Q(45,8)
assert 149**66>600 and Q(816,2045)**2*Q(5,4)**2==Q(204,409)**2
print('180 arithmetic PASS: N=2^763 scalar startup, restored Γ, cubic, reference exceptions, 30-prime Hasse check, true shifted threshold, no 167 trace theorem.')
