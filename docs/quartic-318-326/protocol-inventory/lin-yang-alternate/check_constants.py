#!/usr/bin/env python3
"""Exact conditional arithmetic, not CM/moduli or source-version verification."""
from fractions import Fraction as F
import json

# Q[t]/(t^2+12t+144); irreducible since discriminant -432 < 0.
def pair(a, b=0): return (F(a), F(b))
def add(x, y): return (x[0]+y[0], x[1]+y[1])
def scale(c, x): return (c*x[0], c*x[1])
def mul(x, y):
    a,b=x; c,d=y
    return (a*c-144*b*d, a*d+b*c-12*b*d)
def power(x, n):
    r=pair(1)
    for _ in range(n): r=mul(r,x)
    return r
def norm(x):
    a,b=x
    return a*a-12*a*b+144*b*b
def inv(x):
    a,b=x; n=norm(x)
    assert n != 0
    return ((a-12*b)/n,-b/n)
def divide(x,y): return mul(x,inv(y))
def show(x): return [str(v) for v in x]

t=pair(0,1)
s2=power(add(t,pair(-12)),2)
s3=mul(t,add(add(power(t,2),scale(-36,t)),pair(-432)))
s5=scale(-2**10*3**5,t)
s6=scale(2**10*3**5,add(add(power(t,2),scale(12,t)),pair(12)))
r1=divide(power(s3,2),power(s2,3))
r2=divide(s5,mul(s2,s3))
r3=divide(s6,power(s2,3))
assert r1==pair(F(-16,27))
assert r2==pair(1)
assert r3==pair(F(11,27))
c1=divide(r1,pair(F(-16,27)))
c2=r2
c3=divide(add(r3,pair(-1)),pair(F(-16,27)))
assert c1==c2==c3==pair(1)

# Polynomial coefficients in j, ascending order, to check the weighted Igusa map.
def padd(a,b):
    n=max(len(a),len(b)); a=a+[F(0)]*(n-len(a)); b=b+[F(0)]*(n-len(b))
    return [x+y for x,y in zip(a,b)]
def pmul(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out
def ps(c,a):return [c*x for x in a]
J2=[F(-1),F(-1)]
J4=ps(F(1,24),padd(pmul(J2,J2),[F(0),F(-1)]))
J6=ps(F(1,216),padd(padd(ps(-1,pmul(pmul(J2,J2),J2)),ps(36,pmul(J2,J4))),[F(0),F(0),F(1)]))
J10=[F(0),F(0),F(0),F(-1,2**10*3**5)]
actual=[ps((-12)**w,p) for w,p in zip([1,2,3,5],[J2,J4,J6,J10])]
expected=[[F(12),F(12)],[F(6),F(6),F(6)],[F(4),F(0),F(-8),F(4)],[F(0),F(0),F(0),F(1)]]
assert actual==expected
print(json.dumps({
 'status':'conditional exact arithmetic passed; not independent application acceptance',
 'ring':'Q[t]/(t^2+12t+144)',
 's_values':{k:show(v) for k,v in [('s2',s2),('s3',s3),('s5',s5),('s6',s6)]},
 'nonzero_denominator_norms':{k:str(norm(v)) for k,v in [('s2^3',power(s2,3)),('s2*s3',mul(s2,s3))]},
 'ratios':{k:show(v) for k,v in [('s3^2/s2^3',r1),('s5/(s2*s3)',r2),('s6/s2^3',r3)]},
 'c1_c2_c3_given_c4_1':[show(x) for x in [c1,c2,c3]],
 'weighted_Igusa_scale':-12,
 'weighted_Igusa_coefficients':[[str(v) for v in p] for p in actual],
 'all_pass':True,
 'does_not_check':['Actual optimal CM intersection','Actual CM values','Global modular-form parametrization','Final publication corrections','Integral/metric model or literal318 soundness']
},indent=2)+'\n',end='')
