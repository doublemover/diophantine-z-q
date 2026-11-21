#!/usr/bin/env python3
from fractions import Fraction
from math import gcd,isqrt
import json
A=[2,1,2399,407]
B=[1,1,-1,32]
rows=[]
for p in (11,37):
    sq=sorted({x*x%p for x in range(p)})
    states=[]
    for T in sq:
        g=[i+1 for i,(a,b) in enumerate(zip(A,B)) if (a*T+b)%p==0]
        if (T+1)%p not in sq: continue
        states.append([T,g])
    assert pow(2,(p-1)//2,p)==p-1
    if p==11: assert all(not g for T,g in states)
    else: assert all(g==([2] if T==p-1 else []) for T,g in states)
    rows.append({'prime':p,'square_T_with_square_T_plus_1':states})
def square(q):
    return q>=0 and isqrt(q.numerator)**2==q.numerator and isqrt(q.denominator)**2==q.denominator
def sq_ext_2(q):
    return square(q) or square(q/2)
quartics=[]
for C,B0,classes in ((2399,-4802,(6,6*2399,2399)),(407,-686,(-30,15*407,-2*407))):
    b=Fraction(B0,C)
    q=(b*b-4,2-b,-2-b)
    assert all(square(x/c) for x,c in zip(q,classes))
    assert not any(sq_ext_2(x) for x in q)
    quartics.append({'coefficients':[C,0,B0,0,C],'rational_quadratic_classes':classes})
m,n=41514,1
r,d,s=m*m-n*n,2*m*n,m*m+n*n
assert gcd(r,d)==1 and r*r+d*d==s*s and d%(2*3*17*407)==0
u,v=r*r,d*d
G=[u]+[a*u+b*v for a,b in zip(A,B)]
p=35533
assert all(p%i for i in range(2,isqrt(p)+1)) and pow(2,(p-1)//2,p)==p-1
assert gcd(2*2399*407*d,p)==1 and (u-v)%p
E=[a%(p*p) for a in G]
assert all(x%p!=0 for x in E[:4]) and E[-1]%p==0 and E[-1]!=0
print(json.dumps({'local_saturated_denominator_rows':rows,'quartics':quartics,
                  'first_saturated_example':{'m':m,'n':n,'r':r,'d':d,'s':s,'prime':p,
                                             'G_mod_p2':E,'Delta_num_mod_p':(u-v)%p}},indent=2))
