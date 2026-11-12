#!/usr/bin/env python3
"""Exact finite checks; no inference of global convergence from samples."""
from fractions import Fraction as F
from math import gcd,isqrt
from pathlib import Path
import json

def factor(n):
    out=[];p=2
    while p*p<=n:
        if n%p==0:
            e=0
            while n%p==0:e+=1;n//=p
            out.append((p,e))
        p+=1
    if n>1:out.append((n,1))
    return out

def mu(n):
    fs=factor(n)
    return 0 if any(e>1 for p,e in fs) else (-1)**len(fs)
def rama(q,t):return sum(d*mu(q//d) for d in range(1,gcd(q,t)+1) if gcd(q,t)%d==0)
def histogram(k,q):
    out=[1]+[0]*(q-1)
    for c in [1,1,-1,-1,-k]:
        one=[0]*q
        for x in range(q):one[c*x*x%q]+=1
        nxt=[0]*q
        for a,u in enumerate(out):
            for b,v in enumerate(one):nxt[(a+b)%q]+=u*v
        out=nxt
    return out

def local(k,p,e):
    if e==0:return F(1)
    if p==2:return F(1,8**((e-1)//2)) if e>=3 and e%2 else F(0)
    if k%p==0:return F(p-1,p*p)*F(1,p**(3*((e-1)//2))) if e%2 else F(0)
    return F(p-1,p)*F(1,p**(3*(e//2))) if e%2==0 else F(0)
def coeff(k,q):
    if q==0:return F(0)
    a=F(1)
    for p,e in factor(q):a*=local(k,p,e)
    return a
def density(k,p):
    if p==2:return F(8,7)
    if k%p==0:return F((p+1)**2,p*p+p+1)
    return (1-F(1,p**4))/(1-F(1,p**3))
rows=[]
for k in [318,326]:
    for q in range(1,49):
        h=histogram(k,q);a=F(sum(v*rama(q,t) for t,v in enumerate(h)),q**5)
        assert a==coeff(k,q)
    assert coeff(k,0)==0 and coeff(k,1)==1
    for N in [2,8,16,32,64,128,256]:
        sm=sum((abs(coeff(k,q)) for q in range(N)),F(0))
        ep=F(1)
        for p in range(2,N):
            if factor(p)==[(p,1)]:ep*=density(k,p)
        assert sm<=ep
        rows.append({'kappa':k,'cutoff':N,'global_norm_partial_sum':str(sm),'finite_full_local_product':str(ep),'status':'PASS'})
    for p in [3,5,7,11,53,163]:
        if k%p:
            for e in range(9):assert local(k,p,e)>=0
out={'status':'PASS','direct_original_coefficient_checks':96,'finite_prefix_euler_comparisons':len(rows),'rows':rows,'scope':'Exact finite regression only. Infinite convergence requires the constructed norm Euler products and smooth-number domination in Lean source; not certified by these samples.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS96 original coefficients and14 finite Euler comparisons')
