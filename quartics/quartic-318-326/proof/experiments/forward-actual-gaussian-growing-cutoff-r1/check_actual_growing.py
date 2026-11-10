#!/usr/bin/env python3
"""Exact coefficient/exponent checks and 80-digit tests, not a Lean proof."""
import json,itertools
from fractions import Fraction as F
import mpmath as m
import sympy as s
m.mp.dps=80
counts=dict(symbolic_positive_certificates=0,exceptional_growth=0,log_weight_absorption=0,uniform_normalization=0,growing_cutoff=0,exact_exponent_allocations=0)
b,p,D,X,Z=s.symbols('b p D X Z',nonnegative=True); B=b+1;P=p+1
zero=2*(2*B+1)*((4*B+1)*2*D*X*P+4*(4*B+1))
value=2*D*X*P*((4*B+1)*2*D*Z*P+4*(4*B+1))
for diff in [(60*D*X+120)*B**2*P-zero,(20*D**2*X*Z+40*D*X)*B*P**2-value]:
 assert all(c>=0 for c in s.Poly(s.expand(diff),b,p,D,X,Z).coeffs());counts['symbolic_positive_certificates']+=1
for ep in [F(1,1000),F(1,100),F(1,2),F(1),F(4),F(10)]:
 d=ep/8;e=ep/2
 for lhs,rhs in [(2+2*d+e,F(11,4)+ep),(3+4*d+e,3+ep),(3+d+e,3+ep),(F(11,4)+d+e,F(11,4)+ep)]:
  assert lhs<=rhs;counts['exact_exponent_allocations']+=1
 for k in range(10):
  eta=e/(k+1);assert eta*k<=e and eta*(k+1)==e;counts['exact_exponent_allocations']+=1
assert F(3)+F(1,1000)-F(1,100)==F(2991,1000)<=3-F(1,200)
assert F(11,4)+F(1,1000)<=3-F(1,200)
counts['exact_exponent_allocations']+=2

def le(a,b): assert a<=b*(1+m.mpf('1e-65'))+m.mpf('1e-65'),(str(a),str(b))
def constants(k):
 inner=(2*abs(k)+2)*2088**2+8
 form=(8*abs(k)+4)*2088**2+4
 factor=2*2088**2+4
 coeff=1+form+8*(inner**2+4*2088**2)
 first=1+8*form**2*factor**2+4*2088**4+4*2088**2
 second=1+294**2*109*coeff**9
 return m.mpf(1+first+second)
for bi,k,di,dv in itertools.product([1,2,5,100,10**6],[-326,-1,1,318,326],[m.mpf('.001'),m.mpf('.25'),m.mpf('1')],[m.mpf(1)/3,1,7]):
 B=m.mpf(bi);d=di;D=m.mpf(dv)
 zb=2*(2*B+1)*((4*B+1)*2*D*(abs(k)*(2*B)**2)**d+4*(4*B+1))
 vb=2*D*(4*B**2)**d*((4*B+1)*2*D*(4*(abs(k)+1)*B**2)**d+4*(4*B+1))
 zc=60*D*(4*abs(k))**d+120
 vc=20*D**2*4**d*(4*(abs(k)+1))**d+40*D*4**d
 le(zb,zc*B**(2+2*d));le(vb,vc*B**(1+4*d));counts['exceptional_growth']+=2
for bi,k,gs,ep in itertools.product([1,2,10,10**6,10**30,10**100],[-1,318,326],[[],[0],[1,-1],[0,1,-4,18]],[m.mpf('.001'),m.mpf('.5'),m.mpf('2')]):
 B=m.mpf(bi);eps=ep;d=eps/8;e=eps/2;eta=e/(len(gs)+1)
 W=m.fprod(m.log((2+abs(g))*B**2) for g in gs)
 C=m.fprod(m.log(2+abs(g))+2/eta for g in gs)
 env=m.log(constants(k))+74*m.log(B);E=m.log(constants(k))+74/eta
 le(W,C*B**e);le(W*env,C*E*B**e);counts['log_weight_absorption']+=2
 # D,A,T remain arbitrary positive producers. This tests the exact consuming algebra,
 # not an attempt to compute astronomically large Rankin/divisor constants.
 for D,A,T in [(m.mpf(1)/3,m.mpf(1)/5,m.mpf(2)),(m.mpf(7),m.mpf(11),m.mpf(13))]:
  zb=2*(2*B+1)*((4*B+1)*2*D*(abs(k)*(2*B)**2)**d+4*(4*B+1))
  vb=2*D*(4*B**2)**d*((4*B+1)*2*D*(4*(abs(k)+1)*B**2)**d+4*(4*B+1))
  zc=60*D*(4*abs(k))**d+120
  vc=20*D**2*4**d*(4*(abs(k)+1))**d+40*D*4**d
  main=C*(8*vc+113246208*A)
  error=C*(zc+25401600*A+2*T)+(C*E)*(25930800*A/m.log(3))
  for yi in [3,max(3,abs(k)),max(abs(k),3,int(m.ceil(B**m.mpf('.01'))))]:
   Y=m.mpf(yi)
   opt=A*113246208*B**(3+d)/Y+(A*(25930800*env/m.log(Y)+25401600)+2*T)*B**(m.mpf(11)/4+d)
   full=W*(zb+8*B**2/Y*vb+opt)
   bound=main*B**(3+eps)/Y+error*B**(m.mpf(11)/4+eps)
   le(full,bound);counts['uniform_normalization']+=1
  if eps==m.mpf('.001'):
   Y=max(m.mpf(abs(k)),3,m.ceil(B**m.mpf('.01')))
   assert Y>=3 and Y>=abs(k) and Y>=B**m.mpf('.01')
   le(main*B**(3+eps)/Y+error*B**(m.mpf(11)/4+eps),(main+error)*B**(3-m.mpf(1)/200))
   counts['growing_cutoff']+=1
print(json.dumps({'status':'PASS','precision_digits':80,'checks':counts,'scope':'Exact source-bound algebra and fixed power allocation; numerical tests are not Lean verification; no prime existence asserted.'},sort_keys=True))
