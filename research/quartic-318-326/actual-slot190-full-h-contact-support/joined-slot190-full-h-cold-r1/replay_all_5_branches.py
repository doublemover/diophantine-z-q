#!/usr/bin/env python3
"""Widened contact sieve by direct root symbols and every 5-local square bin."""
from itertools import combinations, product
from math import prod
import json
import sys

D=json.load(open(sys.argv[1]))
A=(2,1,2399,407)
B=(1,1,-1,32)
ps=tuple(D['widened_universe'])
special=(11,37,2399)
def sign(x,p):
    x%=p
    return 0 if not x else (1 if pow(x,(p-1)//2,p)==1 else -1)

def subsets(p):
    return (tuple(r) for k in range(len(p)+1) for r in combinations(p,k))

def states(sat, T5):
    moving = set(ps) - set(sat) - {5,7}
    yieldlists=[]
    for i,(a,b) in enumerate(zip(A,B)):
        root = {p:(-b*pow(a,-1,p))%p for p in moving if a%p and sign(-a*b,p)==1}
        a_odd = a // (2 if i==0 else 1)
        base = a // prod(p for p in moving if a%p==0)
        need5 = sign(a if T5 is None else a*T5+b, 5)
        cand=[]
        for s in subsets(sorted(root)):
            for t in ([1] if need5 else [1,5]):
                v=base*prod(s)*t
                if (v//(2 if i==0 else 1))%24 != a_odd%24 or sign(v,17)!=sign(a,17):
                    continue
                if need5 and sign(v,5)!=need5: continue
                cand.append((v,tuple((p,root[p]) for p in s)))
        yieldlists.append(cand)
    return yieldlists

def cross(i,r,j,s):
    gi,r=r
    gj,s=s
    return all(sign(gj,p)==sign(A[j]*t+B[j],p)!=0 for p,t in r) and all(sign(gi,p)==sign(A[i]*t+B[i],p)!=0 for p,t in s)

out=[]
for sat in subsets(special):
    for t5 in (None,0,1,4):
        C=states(sat,t5)
        live=[()]
        for i,data in enumerate(C):
            live=[(*row,s) for row,s in product(live,data) if all(cross(j,r,i,s) for j,r in enumerate(row))]
        ans=sorted(set(tuple(v for v,_ in s) for s in live))
        out.append({'saturated_11_37_2399':sat,'T5':t5,'individual_counts':list(map(len,C)),'survivors':ans})
print(json.dumps(out,indent=2))
