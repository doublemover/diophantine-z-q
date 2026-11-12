#!/usr/bin/env python3
"""Exact residue histograms and Ramanujan sums; no Lean execution."""
from fractions import Fraction
from math import gcd,isqrt
import json
from pathlib import Path

def histogram(k,q):
    out=[1]+[0]*(q-1)
    for c in [1,1,-1,-1,-k]:
        one=[0]*q
        for x in range(q):one[c*x*x%q]+=1
        nxt=[0]*q
        for a,u in enumerate(out):
            for b,v in enumerate(one):nxt[(a+b)%q]+=u*v
        out=nxt
    assert sum(out)==q**5
    return out

def mobius(n):
    s=1
    for p in range(2,isqrt(n)+1):
        if n%p==0:
            n//=p;s=-s
            if n%p==0:return 0
    return -s if n>1 else s

def ramanujan(q,t):return sum(d*mobius(q//d) for d in range(1,gcd(q,t)+1) if gcd(q,t)%d==0)

rows=[]
for k in [318,326]:
    for p,n in [(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(5,0),(5,1),(7,0),(53,0),(163,0)]:
        m=p**n;q=m*p
        hm=histogram(k,m);hq=histogram(k,q)
        assert [p*a for a in range(m)]==[a for a in range(q) if gcd(a,q)>1]
        for t in range(m):assert sum(hq[t::m])==p**5*hm[t]
        for a in range(m):
            for t in range(q):assert (p*a*t)%q==p*((a*(t%m))%m)
        unit=Fraction(sum(v*ramanujan(q,t) for t,v in enumerate(hq)),q**5)
        difference=Fraction(hq[0],q**4)-Fraction(hm[0],m**4)
        assert unit==difference
        rows.append({'kappa':k,'prime':p,'previous_exponent':n,'modulus':q,'unit_coefficient':str(unit),'count_difference':str(difference),'exact_checks':'PASS'})
out={'status':'PASS','cases':len(rows),'checks':['all-five-coordinate histogram has mass q^5','nonunit frequency image and bijection','p^5 residue fiber multiplicity','standard additive phase descent','literal unit-frequency Ramanujan sum equals exact count-layer difference'],'rows':rows,'scope':'Finite regression only; not Lean or infinite convergence certification.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(rows),'exact prime-power unit-frequency regressions')
