#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import permutations
from math import prod
import json
p=114649; q=119851; B=41579528353; b=4921145; d=p*q*B*b
pairs=[(i,j) for i in range(4) for j in range(i,4)]

def det(A):
    n=len(A)
    return sum((-1)**sum(t[i]>t[j] for i in range(n) for j in range(i+1,n))*
               prod(A[i][t[i]] for i in range(n)) for t in permutations(range(n)))
def subst(A,M):
    return [sum(A[k]*M[k][i]*M[k][j] for k in range(4))*(1 if i==j else 2)
            for i,j in pairs]
def hessian(c):
    A=[[0]*4 for _ in range(4)]
    for (i,j),m in zip(pairs,c):
        if i==j:A[i][j]=2*m
        else:A[i][j]=A[j][i]=m
    return A
def polyadd(a,b):
    ans=[0]*max(len(a),len(b))
    for i,x in enumerate(a):ans[i]+=x
    for i,x in enumerate(b):ans[i]+=x
    return ans
def polymul(a,b):
    ans=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):ans[i+j]+=x*y
    return ans
def pencil(A,B):
    C=[0]*5
    for t in permutations(range(4)):
        sg=(-1)**sum(t[i]>t[j] for i in range(4) for j in range(i+1,4))
        u=[sg]
        for i in range(4):u=polymul(u,[A[i][t[i]],B[i][t[i]]])
        C=polyadd(C,u)
    return C
def invs(C):
    a,r,c,s,e=C
    I=12*a*e-3*r*s+c*c
    J=72*a*c*e-27*a*s*s-27*r*r*e+9*r*c*s-2*c*c*c
    c4=I; c6,rm=divmod(J,2)
    assert rm==0
    DD,rm=divmod(c4*c4*c4-c6*c6,1728)
    assert rm==0
    return c4,c6,DD
def main():
    Q=(q,-p,B,0);R=(q,-9*p,0,b)
    N=((1,0,0,0),(0,1,0,0),(1,1,2,0),(1,1,0,2))
    M=((F(1,2),F(0)),(F(-1,4),F(1,4)))
    assert det(M)*det(N)==F(1,2)
    det0=pencil(hessian(subst(Q,[[int(i==j) for i in range(4)] for j in range(4)])),
               hessian(subst(R,[[int(i==j) for i in range(4)] for j in range(4)])))
    assert det0==[0,-16*d,-160*d,-144*d,0]
    A,C=subst(Q,N),subst(R,N)
    assert all(x%2==0 for x in A) and all((y-x)%4==0 for x,y in zip(A,C))
    At=[x//2 for x in A];Ct=[(y-x)//4 for x,y in zip(A,C)]
    det1=pencil(hessian(At),hessian(Ct))
    i0=invs(det0);i1=invs(det1)
    assert i1==(16*73*d*d,64*595*d**3,2**10*3**4*d**6)
    assert i0==tuple(a*2**e for a,e in zip(i1,(4,6,12)))
    # Normalized negative split to positive via (3y,x,v,3u).
    qplus=(p,-q,-b,0);rplus=(p,-9*q,0,-B)
    switch=((0,3,0,0),(1,0,0,0),(0,0,0,1),(0,0,3,0))
    ident=tuple(tuple(int(i==j) for i in range(4)) for j in range(4))
    assert subst(qplus,switch)==[-x for x in subst(R,ident)]
    assert subst(rplus,switch)==[-9*x for x in subst(Q,ident)]
    print(json.dumps(dict(d=d,negative_original=[Q,R],positive_original=[qplus,rplus],
        normalized_switch=switch,coefficient_index_pairs=pairs,negative_minimal=[At,Ct],
        transformation_quadrics=[["1/2","0"],["-1/4","1/4"]],transformation_variables=N,
        original_hessian_pencil=det0,minimal_hessian_pencil=det1,
        original_invariants_c4_c6_Delta=i0,minimal_invariants_c4_c6_Delta=i1),
          indent=2,sort_keys=True))
if __name__=='__main__':main()
