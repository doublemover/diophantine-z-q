#!/usr/bin/env python3
from pathlib import Path
from fractions import Fraction as Q
from math import prod
import json
H=Path(__file__).resolve().parent; O=H.parent/'forward-prime-crt-sieve-r1'
if (H/'intake.json').exists():
 old=json.loads((O/'intake.json').read_text())
 for n in old['order']:assert (H/(n+'.lean')).read_bytes()==(O/(n+'.lean')).read_bytes(),n
bc=mc=ec=0
for k in range(65):
 for x in [Q(n,32) for n in range(33)]:
  R=(1-x)**k-1+k*x
  assert 0<=R<=k*k*x*x;bc+=1
  for e in [-1,1]:
   D=(1-x)**k*(1-e*x)**2
   assert abs(D-(1-(k+2*e)*x))<=(4*k*k+3*k+1)*x*x;mc+=1
   if x<=Q(1,2) and k*x<=Q(1,2):assert D>=Q(1,8)
 for q in [Q(16*(k+2)+n,1) for n in [0,1,2,7,100,1000]]:
  x=1/q
  for e in [-1,1]:
   nu=q+(q-1)*e
   g=((q-1)*(q-e)*(2*nu+(k-2)*(q-e))+nu*nu-1)/(q**4-1)
   D=(1-x)**k*(1-e*x)**2
   c=(1-g)/D
   assert c>0 and abs(c-1)<=8*(4*k*k+7*k+5)*x*x
   assert c*D==1-g;ec+=1
   # Endpoint perturbations exhaust the supplied first-order error interval.
   for sign in [-1,1]:
    h=(k+2*e)*x+sign*4*(k+1)*x*x
    t=(1-h)/D
    assert t>0 and abs(t-1)<=8*(4*k*k+7*k+5)*x*x;ec+=1
# Without character factors the error is first-order, not summable via p^-2.
k=4;e=1
for q in [Q(1000),Q(10000),Q(100000)]:
 nu=q+(q-1)*e
 g=((q-1)*(q-e)*(2*nu+(k-2)*(q-e))+nu*nu-1)/(q**4-1)
 wrong=(1-g)/(1-1/q)**k
 assert abs(wrong-1)*q>1
print(json.dumps({'binomial_cases':bc,'split_inert_models':mc,'normalized_error_cases':ec,
 'large_threshold':'16(k+2)','negative_control':'omitting character factors leaves first-order error',
 'lean_run':False,'infinite_convergence_numerically_claimed':False},indent=2))
