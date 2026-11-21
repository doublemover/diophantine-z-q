#!/usr/bin/env python3
from fractions import Fraction
from itertools import combinations
import json

G = 63
ROOTS = [Fraction(0), Fraction(-1,2), Fraction(-1), Fraction(1,2399), Fraction(-32,407)]

def inds(a):
    return [i for i in range(a.bit_length()) if a>>i&1]

def subm(a):
    z=a
    while True:
        yield z
        if not z: return
        z=(z-1)&a

def dot(a,b):
    return (a&b).bit_count()%2

def depth7(n):
    def f(i):
        d=0
        while i%7==0:
            i//=7
            d+=1
        return d
    return f(n.numerator)-f(n.denominator)

def rows(adj,S,q,correction=0):
    return [(adj[i]&S)|((dot(adj[i],S)^((q^correction)>>i&1))<<i) for i in inds(S)]

def det(M,S):
    M=M[:]
    for j,i in enumerate(inds(S)):
        k=next((k for k in range(j,len(M)) if M[k]>>i&1),None)
        if k is None: return 0
        M[j],M[k]=M[k],M[j]
        for k in range(j+1,len(M)):
            if M[k]>>i&1: M[k]^=M[j]
    return 1

def link(adj,i,j):
    adj[i]^=1<<j
    adj[j]^=1<<i

Ds = {(i,j):depth7(ROOTS[i]-ROOTS[j]) for i,j in combinations(range(5),2)}
out = {"contact_pair_v7":[[i,j,v] for (i,j),v in Ds.items()],"profiles":[]}
for mu in range(2):
    A=[0]*6
    for i,j in combinations(range(6),2):
        if (mu+Ds.get((i,j),0))%2: link(A,i,j)
    L=rows(A,G,0)
    K=[g for g in range(64) if not any(dot(row,g) for row in L)]
    m=len(K).bit_length()-1
    pivots=[(0,1,2,5),(0,1,2)][mu]
    assert len(pivots)==m
    pbit=sum(1<<j for j in pivots)
    assert len({g&pbit for g in K})==len(K)==1<<m
    assert all(not det(rows(A,G^(1<<j),A[j]),G^(1<<j)) for j in range(6))
    H=((1<<m)-1)<<6
    B=G|H
    z=6+m
    A=A+[0]*(m+1)
    for i,p in enumerate(pivots):
        link(A,p,6+i)
        link(A,6+i,z)
    qold=pbit|((m%2)<<z)
    bmark=G|(1<<z)
    assert not dot(qold,bmark)
    coefs={J:0 for J in subm(B)}
    for h in subm(H):
        q=qold|h
        M=rows(A,B|(1<<z),q)
        assert all(not dot(r,bmark) for r in M)
        assert det(rows(A,B|(1<<z),q,1<<z),B|(1<<z))
        for J in coefs:
            S=B^J
            coefs[J]^=det(rows(A,S,q),S)
    nonzero=[J for J in coefs if coefs[J]]
    assert nonzero==[G]
    assert [J for J in sorted(subm(G)) if det(rows(A,G^J,0),G^J)]==[G]
    out["profiles"].append({"mu":mu,"binary_laplacian":L,"kernel":K,
        "pivots":list(pivots),"helper_count":m,
        "all_sharp_native_switches":1<<m,
        "full_x_derivative_nonzero_on_deletion_masks":nonzero,
        "isolated_reference_nonzero_on_deletion_masks":[G]})
print(json.dumps(out,indent=2,sort_keys=True))
