#!/usr/bin/env python3
"""Independent exact arithmetic; no CM-point, modular-parametrization or repair theorem."""
from fractions import Fraction as F
from pathlib import Path
import json, hashlib
ROOT=Path('/workspace/scratch/2cb21e4e0864')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
target=ROOT/'recovery-hodge-0358/baba-granath-alternate-review/receipt.json'
assert sha(target)=='9f5ca044f025377a45c33ce9f609e8615d714d07f7092afaa6f494c1b6afdf38'
assert sha(ROOT/'v13-lin-yang-review/source-cache/lin-yang-v1.pdf')=='773518a4a30e4f4acac650b7f7c5f19decfb1f893431e6d04f4cfd0205919038'
# Polynomials in t, reduced by t^2=-12t-144; a separate implementation from author checker.
def reduce(a):
 a=list(map(F,a))
 while len(a)>2:
  c=a.pop(); a[-1]-=12*c; a[-2]-=144*c
 return (a+[F(0),F(0)])[:2]
def times(a,b):
 r=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):r[i+j]+=x*y
 return r
def powpoly(a,n):
 r=[F(1)]
 for _ in range(n):r=times(r,a)
 return r
s2=reduce([144,-24,1]);s3=reduce([0,-432,-36,1]);s5=reduce([0,-2**10*3**5]);s6=reduce([12*2**10*3**5,12*2**10*3**5,2**10*3**5])
assert s2==[0,-36] and s3==[6912,0] and s6==[-32845824,0]
assert reduce([0,0,0,1])==[1728,0]
a=reduce(powpoly(s2,3));b=reduce(times(s2,s3));assert a[0]!=0 and b[1]!=0
# t!=0 follows from polynomial constant144; therefore b!=0.
ratios=[F(s3[0]**2,a[0]),F(s5[1],b[1]),F(s6[0],a[0])]
assert ratios==[F(-16,27),F(1),F(11,27)]
constants=[ratios[0]/F(-16,27),ratios[1],(ratios[2]-1)/F(-16,27)]
assert constants==[1,1,1]
# Independent reconstruction of weighted Igusa tuple as polynomial equalities.
J2=[F(-1),F(-1)]
J4=[F(1,24),F(1,24),F(1,24)]
J6=[F(-1,432),0,F(2,432),F(-1,432)]
J10=[0,0,0,F(-1,248832)]
def add(*polys):
 r=[F(0)]*max(map(len,polys))
 for p in polys:
  for i,c in enumerate(p):r[i]+=c
 return r
def sc(c,p):return [c*x for x in p]
assert add(sc(24,J4),sc(-1,times(J2,J2)),[0,1])==[0,0,0]
assert add(sc(216,J6),powpoly(J2,3),sc(-36,times(J2,J4)),[0,0,-1])==[0,0,0,0]
weighted=[sc(F(-12)**w,p) for w,p in zip([1,2,3,5],[J2,J4,J6,J10])]
assert weighted==[[12,12],[6,6,6],[4,0,-8,4],[0,0,0,1]]
# The declared f's cannot have the printed Hauptmodul ratio.
weight_f1=2*2;weight_f2=(6+6)*F(1,2)
q_order_f1=0;q_order_f2=6*F(1,24)+6*F(5,24)
q_order_etaquot=6*F(1,24)-6*F(5,24)
assert weight_f1-weight_f2==-2
assert q_order_f1-q_order_f2==F(-3,2)
assert q_order_etaquot==-1
assert (1-5)**2==16
# Weighted invariant obstruction to changing linear s5 into quadratic s5.
# s5^2/s2^5 has total weight0. Altered s5 multiplies this by t^2, not1.
assert reduce([-1,0,1])!=[0,0]
print(json.dumps({'status':'PASS bounded exact arithmetic and source-pin checks',
 'target_receipt_sha256':sha(target),'s2':list(map(str,s2)),'s3':list(map(str,s3)),'s5':list(map(str,s5)),'s6':list(map(str,s6)),
 't_cubed':'1728','s2_cubed':str(a[0]),'denominator_check':'s2^3=-80621568; s2*s3=-248832t; t!=0',
 'ratios':list(map(str,ratios)),'c1_c2_c3_given_c4_1':list(map(str,constants)),
 'weighted_Igusa_tuple_coefficients':[[str(x) for x in p] for p in weighted],
 'printed_ratio_weight':str(weight_f1-weight_f2),'printed_ratio_leading_q':'16q^(-3/2)',
 'eta_Hauptmodul_leading_q':'q^(-1)','s5_tuple_weighted_invariant_change':'factor t^2 in s5^2/s2^5',
 'not_checked':['actual optimal CM point or its t value','global modular parametrization','corrected f1/f2','final published main body','global D6 or D210 theorem']},indent=2))
