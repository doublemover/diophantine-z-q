#!/usr/bin/env python3
from itertools import product
import json,mpmath as mp,sympy as s
mp.mp.dps=75
c=dict(coefficient_growth=0,first_height_degree18=0,second_height_degree74=0,
 common_height_logs=0,combined_source_budget=0,threshold_bounds=0,
 optimized_power_identity=0,symbolic_growth_certificates=0)
def constants(k):
 j=(2*abs(k)+2)*2088**2+8
 f=(8*abs(k)+4)*2088**2+4;n=2*2088**2+4
 a=1+f+8*(j*j+4*2088**2)
 c1=1+8*f*f*n*n+4*2088**4+4*2088**2
 c2=1+294**2*109*a**9
 return j,f,n,a,c1,c2,1+c1+c2
def literal(k,t,R):
 L=58*R*R
 F=(2*abs(k)*(abs(t)+2)+4)*L*L+2*abs(t);N=2*L*L+t*t
 J=(2*abs(k)+2)*L*L+t*t+2*abs(t)
 A=1+F+8*(J*J+t*t*L*L)
 return F,N,J,A,1+8*F*F*N*N+4*L**4+t*t*L*L,1+(49*R)**2*109*A**9
for k,B in product([-326,-1,0,1,2,318,326],range(1,41)):
 j,f,n,a,c1,c2,C=constants(k);F,N,J,A,G1,G2=literal(k,2*B,6*B)
 assert F<=f*B**5 and N<=n*B**4 and J<=j*B**4 and A<=a*B**8
 c['coefficient_growth']+=1
 assert G1<=c1*B**18;c['first_height_degree18']+=1
 assert G2<=c2*B**74;c['second_height_degree74']+=1
 env=mp.log(C)+74*mp.log(B)
 assert mp.log(G1)<=env and mp.log(G2)<=env;c['common_height_logs']+=1
 T=mp.power(B,mp.mpf(3)/4)
 assert T>0 and T<=6*B;c['threshold_bounds']+=1
 for Y in [3,5,17,101]:
  logY=mp.log(Y);R=6*B
  v1=mp.mpf(262144)*R**3/Y*logY+480200*R*R*T*mp.log(G1)+352800*R*R*T*logY
  v2=mp.mpf(262144)*R**3/Y*logY+240100*R*R*T*mp.log(G2)+352800*R*R*T*logY
  comb=mp.mpf(113246208)*B**3/Y*logY+25930800*B*B*T*env+25401600*B*B*T*logY
  assert v1+v2<=comb+mp.mpf('1e-60');c['combined_source_budget']+=1
  for delta,rankin,tail,W in [(mp.mpf('.1'),mp.mpf(13),mp.mpf(7),mp.mpf(1)),
      (mp.mpf('.5'),mp.mpf(31),mp.mpf(11),mp.mpf(5)),(mp.mpf(2),mp.mpf(17),mp.mpf(19),mp.mpf(0))]:
   rc=2*rankin*mp.power(2,delta)
   lhs=(2*rankin*mp.power(2*B,delta)*comb*W+
        2*tail*mp.power(B,mp.mpf(11)/4+delta)*W*logY)/logY
   rhs=W*(rc*113246208*mp.power(B,3+delta)/Y+
     (rc*(25930800*env/logY+25401600)+2*tail)*mp.power(B,mp.mpf(11)/4+delta))
   assert abs(lhs-rhs)<=mp.mpf('1e-60')*max(1,abs(lhs));c['optimized_power_identity']+=1
# Universal coefficientwise positivity after B=1+u,kappa-absolute=a.
u,a=s.symbols('u a',nonnegative=True);B=u+1;L=2088*B**2
J=(2*a+2)*L**2+4*B**2+4*B;F=(2*a*(2*B+2)+4)*L**2+4*B;N=2*L**2+4*B**2
jc=(2*a+2)*2088**2+8;fc=(8*a+4)*2088**2+4;nc=2*2088**2+4
Ac=1+fc+8*(jc**2+4*2088**2);A=1+F+8*(J**2+4*B**2*L**2)
for expr in [fc*B**5-F,nc*B**4-N,jc*B**4-J,Ac*B**8-A]:
 p=s.Poly(s.expand(expr),u,a)
 assert all(v>=0 for v in p.coeffs());c['symbolic_growth_certificates']+=1
assert 2*262144*6**3==113246208
assert (480200+240100)*6**2==25930800
assert 2*352800*6**2==25401600
print(json.dumps({'status':'PASS','checks':c,'real_precision_digits':75,
 'actual_true_quartic_height_degree':74,'valid_first_chart_height_degree':18,
 'threshold':'B^(3/4)','local_lean':'NOT_RUN'},indent=2))
