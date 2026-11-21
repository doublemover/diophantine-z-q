"""Independent tuple-field kernels, Lucas matrix and exact W numerators."""
from fractions import Fraction as Q
from math import gcd,isqrt,prod
from pathlib import Path
from hashlib import sha256
import json,sys
sys.set_int_max_str_digits(0)
hashes=(
 'ed565029774c021709d547e28545ca14cf3a5dc0eb209f098bdcf2e84008ab9b',
 'fa445c7cdc40b5e5ba35d2e389d5d81a2f2d95985a25546e1a41c8e0649e993f',
 'e2ae32e04432f61f66109a63faa01ea1b5e90d2d21411227d30fa58fcdd65823',
 'f5dbe608ef26c9bde7a3ff31f40770ba9924fd4e9071e49520761ac3f39e7b64',
)
raw=[Path(f).read_bytes() for f in sys.argv[1:]]
assert tuple(sha256(x).hexdigest() for x in raw)==hashes
inp,idx,expected,repair=map(json.loads,raw)
W=Q(*inp['W']);Y=Q(*inp['Y']);h=idx['h'];qa=inp['qa']
assert W>2 and W*W-Q(-32,407)==inp['pa']*qa*Q(inp['cofactor_square_root'],W.denominator)**2
assert W*W-Q(1,2399)==inp['b']*Y**2
assert sha256(str(qa).encode()).hexdigest()=='b5bf27f831d44eeaaf06f5356cce9d861e69964846d9d462d950e86155f12e26'
J=int(repair['literal_J'])
S=1+6**15*3**65536*J; index=2*(S-2); bits=bin(index)[2:]
def prime_factors(n):
 for i in range(2,isqrt(n)+1):
  if n%i==0:
   yield i
   while n%i==0:n//=i
 if n>1:yield n
def mat(a,b,n):
 x,y,z,w=a;r,s,t,u=b
 return ((x*r+y*t)%n,(x*s+y*u)%n,(z*r+w*t)%n,(z*s+w*u)%n)
def labels(n):
 g,d=1,S-2
 while (f:=gcd(d,n))>1:g*=f;d//=f
 m=n*g
 r=(1,0,0,1); a=(0,1,m-1,S%m)
 for bit in reversed(bits):
  if bit=='1':r=mat(a,r,m)
  a=mat(a,a,m)
 assert r[1]%g==0
 return tuple(x%n for x in (3723,S,r[3],r[1]//g*pow(d,-1,n)))
def mod(q,M):
 q=Q(q);return q.numerator*pow(q.denominator,-1,M)%M
out=[]
for E in expected['fatal']:
 p=E['p']; M=p*p; order=E['arm_order']
 assert list(prime_factors(p))==[p] and p%8==3 and pow(2,(p-1)//2,p)==p-1
 class A:
  def __init__(self,a=0,b=0): self.x=a%M;self.y=b%M
  def __add__(self,z):
   if not isinstance(z,A):z=A(z)
   return A(self.x+z.x,self.y+z.y)
  __radd__=__add__
  def __neg__(self):return A(-self.x,-self.y)
  def __sub__(self,z):return self+(-z)
  def __rsub__(self,z):return -self+z
  def __mul__(self,z):
   if not isinstance(z,A):z=A(z)
   return A(self.x*z.x+2*self.y*z.y,self.x*z.y+self.y*z.x)
  __rmul__=__mul__
  def n(self):return (self.x*self.x-2*self.y*self.y)%M
  def inv(self):return pow(self.n(),-1,M)*A(self.x,-self.y)
  def __truediv__(self,z):return self*z.inv()
  def __pow__(self,n):
   r=A(1)
   for _ in range(n):r=r*self
   return r
  def unit(self):return bool(self.x%p or self.y%p)
  def one_mod(self):return self.x%p==1 and not self.y%p
  def val(self):return int(not self.unit()) if self.x or self.y else 999
  def out(self,m=M):return [self.x%m,self.y%m]
 r=A(0,1);D=(3-r)**2
 R=(1+r,2*r)
 def add(P,Q):
  if len(P)==1:
   if len(Q)==1:return (P[0]+Q[0],)
   z=P[0];x,y=Q
   return (x+2*y*z,y+(3*x*x-D)*z)
  if len(Q)==1:return add(Q,P)
  x,y=P;u,v=Q
  sec=x*x+x*u+u*u-D
  if (u-x).unit():w=(v-y)/(u-x)
  elif (v-y).unit():return ((u-x)/(v-y),)
  elif (v+y).unit():w=sec/(v+y)
  else:return ((v+y)/sec,)
  X=w*w-x-u
  return (X,w*(x-X)-y)
 def mul(n):
  P=(A(),)
  for z in bin(n)[2:]:
   P=add(P,P)
   if z=='1':P=add(P,R)
  return P
 z=mul(order)
 assert len(z)==1 and all(len(mul(order//ell))==2 for ell in prime_factors(order))
 def chart(n):
  P=mul(n%(p*order))
  if len(P)==1:
   # Only residue field used on formal returns here.
   return A(),A(1)
  x,y=P; x2=x*x; L=x2+D
  return 2*y/L,(x2*x2-6*D*x2+D*D)/(L*L)
 lab=labels(p*order)
 Uv=[chart(j)[0] for j in lab]
 assert all(t.unit() for t in Uv)
 P0=prod((-u.inv() for u in Uv),start=A(1))
 scales=[1,(P0.x+P0.n())%M,P0.n()]
 assert scales==E['scales_p2'] and all(s%p for s in scales)
 T=pow(mod(W,M),2,M)
 F=prod(T-mod(s,M) for s in (0,Q(-1,2),-1,Q(-32,407),Q(1,2399)))%M
 assert F%p==0 and F!=0 and (T-1)%p and T==E['literal_T_mod_p2'] and F==E['F_mod_p2']
 U,V=chart(h)
 assert U.unit() and U.out(p)==E['actual_U_h_mod_p'] and V.out(p)==E['actual_V_h_mod_p']
 k=-1+mod(Q(7,4),M)*r;m=mod(Q(39,8),M)+mod(Q(-9,2),M)*r
 S0=(k*V/U-m)/(k*k+D*U*U)
 G=U*U*S0*S0
 B=k*k+m*S0+D*G
 x=D*G*G
 PG=1+mod(Q(-61,65),M)*x+mod(Q(16,195),M)*x*x
 QG=1+mod(Q(-7,13),M)*x
 CC=k*S0*PG/(QG*B)
 assert [r.n()%p for r in (PG,QG,CC)]==E['PG_QG_common_norm_mod_p']
 assert all(t.unit() for t in (PG,QG,CC))
 prim=[chart(j*h)[1].n()%p for j in lab]
 alt=[(1+mod(Q(5,13),M)*(chart(j*(h-1))[1]-1)).n()%p for j in lab]
 assert prim==E['primary_V_norm_mod_p'] and alt==E['alternate_QJ_norm_mod_p']
 assert all(prim) and all(alt[1:])
 # First leaf rational with nonzero reduction after removing p^-7.
 lower=[-7,-1,-1]+[-25]*13
 depths=[0]
 for lb in lower:
  if len(depths)==1:assert lb<2*depths[-1];depths.append(lb)
  else:assert 2*depths[-1]<lb;depths.append(2*depths[-1])
 v_fold=depths[-1]; v_value=1+2*v_fold
 assert v_fold==E['fold_and_trace_depth'] and v_value==-458751
 out.append(dict(p=p, order=order, normalized_middle_value_depth=v_value,
                 square_reduced_denominator=False, source_chart_and_pade_mod_p_confirmed=True))
print(json.dumps(out,indent=2))
