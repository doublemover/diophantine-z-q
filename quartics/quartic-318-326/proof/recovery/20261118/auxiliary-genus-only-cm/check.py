"""Exact Laplacian, class number and two-edge controls; pure Python, no CAS."""
from math import isqrt,gcd,prod
from itertools import product
import json
def kernel(L):
 return [x for x in product(range(2),repeat=len(L)) if all(not(sum(a*b for a,b in zip(r,x))%2) for r in L)]
def lap(P):
    assert len(P)==len(set(P)) and all(p>2 and all(p%u for u in range(2,isqrt(p)+1)) for p in P)
    L=[[0 if i==j else int(pow(a,(p-1)//2,p)==p-1) for j,a in enumerate(P)] for i,p in enumerate(P)]
    for i,r in enumerate(L):r[i]=sum(r)%2
    return L
def count(d):
    h=0
    for a in range(1,isqrt(d//3)+1):
        for b in range(-a+(not a%2),a+1,2):
            if (b*b+d)%(4*a):continue
            c=(b*b+d)//(4*a)
            h+=int(c>=a and (b>=0 or (b!=-a and c!=a)) and gcd(a,gcd(b,c))==1)
    return h
def check(P,k):
    L=lap(P); LL=lap(P+[k]);B=kernel(L);R=kernel(list(zip(*L))); vv=LL[-1][:-1];i,j=[i for i,x in enumerate(vv) if x]
    assert len(B)==len(R)==4 and B[1][i]!=B[1][j] and R[1][i]!=R[1][j]
    assert len(kernel(LL))==2
    return dict(P=P,k=k,dual=R[1],primal=B[1],new_edges=[P[i],P[j]],new_matrix=LL,old_h=count(prod(P)),new_h=count(prod(P)*k))
A=check([127,17,409],73)
assert A['old_h']==1032 and A['new_h']==7368 and (A['new_h']//8)%2==1
# The scalar-style nonsymmetric earlier matrix: find a CRT-admissible two-edge prime.
P=[79,11,19,13]; B=kernel(lap(P))[1];R=kernel(list(zip(*lap(P))))[1]
assert B not in (R,tuple(1-i for i in R))
i,j=next((i,j) for i in range(len(P)) for j in range(i) if B[i]!=B[j] and R[i]!=R[j])
k=next(k for k in range(73,40000,24) if all(k%v for v in range(2,isqrt(k)+1)) and all((pow(k,(p-1)//2,p)==p-1)==(ii in (i,j)) for ii,p in enumerate(P)))
# Pure binary check only for this nonsplit-at-2 control; avoid a redundant large form count.
assert len(kernel(lap(P+[k])))==2
print(json.dumps(dict(actual_template=A,nonsymmetric_test=dict(old=P,new_k=k,primal=B,dual=R,edges=[P[i],P[j]])),indent=2))
