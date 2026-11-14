#!/usr/bin/env python3
"""Exact cyclic-group-ring regressions; not Lean or analytic estimates."""
from collections import defaultdict
from itertools import product
from pathlib import Path
import json

def Q(k,x):
    return x[0]**2+x[1]**2-x[2]**2-x[3]**2-k*x[4]**2

def bilinear(k,h,y):
    return h[0]*y[0]+h[1]*y[1]-h[2]*y[2]-h[3]*y[3]-k*h[4]*y[4]

def conv(a,b,q):
    c=[0]*q
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[(i+j)%q]+=x*y
    return c

def poly(q,points,k,weights):
    p=[0]*q
    for x in points: p[Q(k,x)%q]+=weights[x]
    return p

def run():
    counts=dict(polarization=0,weighted_correlation=0,box_products=0,zero_phase=0,geometric_telescoping=0,quadratic_shifts=0,negative_controls=0)
    samples=[[],[(0,)*5],list(product((-1,1),repeat=5)),
             [(i-2,i%3-1,2-i,i%2,i-3) for i in range(6)]]
    for q in (1,2,3,4,5,8,9,12):
        for k in (-7,-1,0,1,2,7):
            for points in samples:
                weights={x:sum((j+1)*x[j] for j in range(5))-2 for x in points}
                p=poly(q,points,k,weights)
                lhs=conv(p,[p[-i%q] for i in range(q)],q)
                correlations=defaultdict(lambda:[0]*q)
                for x in points:
                    for y in points:
                        h=tuple(a-b for a,b in zip(x,y))
                        phase=2*bilinear(k,h,y)
                        assert Q(k,x)-Q(k,y)==Q(k,h)+phase
                        counts['polarization']+=1
                        correlations[h][phase%q]+=weights[x]*weights[y]
                rhs=[0]*q
                for h,c in correlations.items():
                    for r,a in enumerate(c): rhs[(Q(k,h)+r)%q]+=a
                assert lhs==rhs
                counts['weighted_correlation']+=1
                assert sum(rhs)==sum(weights.values())**2
                counts['zero_phase']+=1
            for intervals in [([0],[1],[-1],[2],[-2]),
                ([-2,-1],[0,1],[-1,1],[-1,0],[1,2]),
                ([],[0],[0],[0],[0])]:
                points=list(product(*intervals))
                actual=poly(q,points,k,{x:1 for x in points})
                factored=[1]+[0]*(q-1)
                for c,s in zip((1,1,-1,-1,-k),intervals):
                    f=[0]*q
                    for x in s: f[c*x*x%q]+=1
                    factored=conv(factored,f,q)
                assert actual==factored
                counts['box_products']+=1
    for q in (1,2,3,4,5,8,9,12):
        for c in (-7,-1,0,1,2,7):
            for h in (-3,-1,0,1,4):
                for m in (-5,0,3):
                    for N in (0,1,2,7,13):
                        paired=[0]*q
                        linear=[0]*q
                        geometric=[0]*q
                        for j in range(N):
                            paired[(c*(m+j+h)**2-c*(m+j)**2)%q]+=1
                            linear[(c*h*h+2*c*h*(m+j))%q]+=1
                            geometric[c*j%q]+=1
                        assert paired==linear
                        counts['quadratic_shifts']+=1
                        factor=[0]*q;factor[c%q]+=1;factor[0]-=1
                        expected=[0]*q;expected[c*N%q]+=1;expected[0]-=1
                        assert conv(factor,geometric,q)==expected
                        counts['geometric_telescoping']+=1
    # Deliberate wrong sign, missing factor two, altered weight and phase:
    # each must change the exact group-ring coefficient vector.
    q=11;k=3;x=(1,2,0,-1,2);y=(0,1,-2,0,1)
    h=tuple(a-b for a,b in zip(x,y))
    assert (Q(k,x)-Q(k,y))%q != (Q(k,h)+bilinear(k,h,y))%q
    assert (Q(k,x)-Q(k,y))%q != (Q(-k,h)+2*bilinear(-k,h,y))%q
    points=[x,y]; weights={x:2,y:-3}
    a=poly(q,points,k,weights)
    correct=conv(a,[a[-i%q] for i in range(q)],q)
    b=poly(q,points,k,{x:2,y:3})
    assert correct!=conv(b,[b[-i%q] for i in range(q)],q)
    assert correct!=conv(a,a,q)
    counts['negative_controls']+=4
    result={'status':'PASS','scope':'Exact integer cyclic group-ring identities at finite moduli, not Lean verification, Weyl decay, minor-arc integration or prime production','checks':counts}
    Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__': run()
