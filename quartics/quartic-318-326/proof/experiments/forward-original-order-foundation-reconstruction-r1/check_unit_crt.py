#!/usr/bin/env python3
"""Exact unit CRT domains/phases and five-coordinate residue histograms."""
from fractions import Fraction
from math import gcd,isqrt
from pathlib import Path
import json

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

def mu(n):
    s=1
    for p in range(2,isqrt(n)+1):
        if n%p==0:
            n//=p;s=-s
            if n%p==0:return 0
    return -s if n>1 else s

def ramanujan(q,t):return sum(d*mu(q//d) for d in range(1,gcd(q,t)+1) if gcd(q,t)%d==0)
def coeff(k,q,hh):return Fraction(sum(v*ramanujan(q,t) for t,v in enumerate(hh)),q**5)
rows=[]
for k in [318,326]:
    for m,n in [(1,1),(1,8),(2,3),(4,3),(4,9),(8,9),(3,5),(9,5),(5,7),(8,5),(2,53),(2,163)]:
        assert gcd(m,n)==1;q=m*n
        um=[a for a in range(m) if gcd(a,m)==1];un=[b for b in range(n) if gcd(b,n)==1]
        merged=[(n*a+m*b)%q for a in um for b in un]
        assert len(merged)==len(set(merged))
        assert set(merged)=={a for a in range(q) if gcd(a,q)==1}
        for a in um:
            for b in un:
                for t in range(q):assert ((n*a+m*b)*t)%q==(n*((a*(t%m))%m)+m*((b*(t%n))%n))%q
        hm=histogram(k,m);hn=histogram(k,n);hq=histogram(k,q)
        for t in range(q):assert hq[t]==hm[t%m]*hn[t%n]
        am=coeff(k,m,hm);an=coeff(k,n,hn);aq=coeff(k,q,hq);assert aq==am*an
        rows.append({'kappa':k,'m':m,'n':n,'unit_count':len(merged),'coefficient_mn':str(aq),'product':str(am*an),'status':'PASS'})
out={'status':'PASS','cases':len(rows),'checks':['cross-scaled frequency bijection on complete unit domains','standard character exponents exactly modulo mn','all-five-coordinate original residue distribution CRT','q^-5 literal unit coefficient multiplicativity'],'rows':rows,'scope':'Exact finite regressions only; not Lean or global infinite-series acceptance.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS',len(rows),'exact unit-CRT regressions')
