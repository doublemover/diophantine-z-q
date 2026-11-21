#!/usr/bin/env python3
"""Exact p^3 computation and all 25 affine residue classes at p=5."""
from contextlib import redirect_stdout
from fractions import Fraction as Q
from functools import reduce
from hashlib import sha256
from io import StringIO
from pathlib import Path
import json,runpy
base=Path(__file__).resolve().parent.parent
def pin(path,h):
    f=base/path
    assert sha256(f.read_bytes()).hexdigest()==h
    return f
with redirect_stdout(StringIO()):
    d=runpy.run_path(str(pin('linked-detector-two-class-fixed-selmer-quotient-r1/check_fixed_quotient_known_rows.py',
      '082b8c90ee5afc55c27d0bc042457eaff9f4c5f37294bce387e7eee4aab92150')))
d['labels'].__globals__['s']=1+d['i']
ord5,point,chart,formal=d['F'](5,None)
assert formal(point(5)) and not formal(point(1)) and ord5()==5
ns=d['labels'](125,(5,))
assert ns==[98,1,124,1]
def add(x,y):a,b=x;c,d=y;return a+c,b+d
def sub(x,y):a,b=x;c,d=y;return a-c,b-d
def mul(x,y):a,b=x;c,d=y;return a*c+2*b*d,a*d+b*c
def div(x,y):
    a,b=y;D=a*a-2*b*b
    return mul(x,(a/D,-b/D))
def sc(a,n):return a[0]*n,a[1]*n
sq=lambda a:mul(a,a)
R=((Q(1),Q(1)),(Q(0),Q(2)))
D=(Q(11),Q(-6))
def padd(P,Q):
    if not P:return Q
    if not Q:return P
    x,y=P;X,Y=Q
    if x==X:
        if y!=Y or not any(y):return None
        slope=div(sub(sc(sq(x),3),D),sc(y,2))
    else:slope=div(sub(Y,y),sub(X,x))
    z=sub(sub(sq(slope),x),X)
    zz=sub(mul(slope,sub(x,z)),y)
    assert sq(zz)==sub(mul(sq(z),z),mul(D,z))
    return z,zz
def pmul(n):
    A=None;B=R
    while n:
        if n&1:A=padd(A,B)
        n//=2
        if n:B=padd(B,B)
    return A
def U(n):
    x,y=pmul(n)
    return div(sc(y,2),add(sq(x),D))
def mod(q,M):return (q.numerator*pow(q.denominator,-1,M))%M
def qm(z,M):return mod(z[0],M),mod(z[1],M)
def imul(x,y,M):
    a,b=x;c,d=y
    return ((a*c+2*b*d)%M,(a*d+b*c)%M)
Urows=[qm(U(n),125)for n in ns]
A,B=reduce(lambda x,y:imul(x,y,125),Urows,(1,0))
eta=(1+A)%125
c2=pow((A*A-2*B*B)%125,-1,125)
assert (A,B,eta,c2)==(34,124,35,69)
e=eta//5
S=-32*407*2399**2%25
T5=2399*407**2*e*e%25
C5=(2399*407*c2*e)**2%25
u=pow(2399,-1,25)
assert (S,T5,C5,u)==(1,24,11,24)
rows=[]
for k in range(25):
    if not k%5:continue
    w=(k*k-S*T5)**2*pow(4*k*(5*k-S)*(k-5*T5)*C5,-1,25)%25
    value=(w-u)%25
    if k%5 in (1,4):assert w==9 and value==10
    else:assert value%5==1
    rows.append((k,w,value))
# The p_c/q_c two-orbit correction uses D NONsquare, not minus one.
t=json.loads(pin('linked-detector-three-class-local-after-selmer4-r1/EXACT-THIRD-PILOT-AND-ANCHOR.json',
 '8d4e41c9f6db7036cdb72284216b2502def7bbaa54074b793e517c542d8d8db2').read_bytes())
p=t['p_c'];s=t['scaled_roots_mod_p'][1][3];t0=t['scaled_roots_mod_p'][2][2]
chi=lambda z:1 if pow(z%p,(p-1)//2,p)==1 else -1
assert [chi(z)for z in [s,t0,s-t0]]==[-1,1,-1]
Aphase,Bphase=t['unit_quotient_a_b_bits']
assert (Aphase,Bphase)==(1,-1)
es=[0,s,t0]
twist=next(q for q in range(1,p)if chi(q)==-1)
tw=[twist*q%p for q in es]
pairs=[]
for i in range(3):
    row=[tw[i]-tw[j] for j in range(3)]
    row[i]=row[(i+1)%3]*row[(i+2)%3]
    pairs.append(tuple(chi(q)for q in row))
assert pairs==[(-1,1,-1),(1,1,1),(-1,1,-1)]
print(json.dumps({'exact_p5_period':125,'labels':ns,'U_mod125':Urows,'eta_mod125':eta,
                  'c2_mod125':c2,'scale_roots_target_mod25':[S,T5,C5,u],
                  'five_digit_rows':rows,'third_primes_pair_torsion_rows':pairs,
                  'third_primes_pair_alpha':[-1,-1,1]},indent=2))
