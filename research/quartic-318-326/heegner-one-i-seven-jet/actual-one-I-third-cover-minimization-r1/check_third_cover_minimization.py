#!/usr/bin/env python3
"""Concrete deterministic transformations of the same ξ-lift; no point search."""
import json,sys
from fractions import Fraction as F
from pathlib import Path
from itertools import product
from math import isqrt
H=Path(__file__).resolve().parent
RAW=H.parent/'actual-one-I-explicit-third-isogeny-cover-r1'
BASE=H.parent/'actual-one-I-split-isogeny-selmer-r1'
sys.path.insert(0,str(BASE))
from check_actual_minimal_intersection import d,p,q,hessian,pencil,invs,pairs,det

def mat(q):
    A=[[F(0) for j in range(4)] for i in range(4)]
    for i,j in pairs:
        a=q[pairs.index((i,j))]
        if i==j:A[i][i]=F(a)
        else:A[i][j]=A[j][i]=F(a,2)
    return tuple(tuple(a for a in r) for r in A)
def coeff(A):
    Q=[]
    for i,j in pairs:
        u=A[i][j]*(1 if i==j else 2)
        assert u.denominator==1
        Q.append(u.numerator)
    return Q
def mm(A,B):
    return tuple(tuple(sum(a*b for a,b in zip(r,c)) for c in zip(*B)) for r in A)
def ident(n):
    return tuple(tuple(F(int(i==j)) for j in range(n)) for i in range(n))
def add(A,B):
    return tuple(tuple(a+b for a,b in zip(r,s)) for r,s in zip(A,B))
def sc(c,A):
    return tuple(tuple(c*a for a in r) for r in A)
def tr(A):return tuple(zip(*A))
def change(V,Q,N):
    A,B=Q
    l,r=V[0];t,u=V[1]
    out=tuple(mm(tr(N),mm(C,N)) for C in (add(sc(l,A),sc(r,B)),add(sc(t,A),sc(u,B))))
    [coeff(M) for M in out]
    return out
def change_unsafe(V,Q,N):
    A,B=Q
    l,r=V[0];t,u=V[1]
    return tuple(mm(tr(N),mm(C,N)) for C in (add(sc(l,A),sc(r,B)),add(sc(t,A),sc(u,B))))
def block(S,i):
    P=[list(r) for r in ident(4)]
    for r,c in product(range(2),repeat=2):P[i+r][i+c]=F(S[r][c])
    return tuple(tuple(r) for r in P)
def evalpart(Q,x,y,i):
    return Q[i][i]*x*x+2*Q[i][i+1]*x*y+Q[i+1][i+1]*y*y
def rootpair(Q,P,i):
    for x,y in [(x,1) for x in range(P)]+[(1,0)]:
        if all(evalpart(A,x,y,i).numerator%P==0 for A in Q):return x,y
    return None
def shift_line(P,x,y):
    if y:return ((P,x),(0,1))
    return ((1,0),(0,P))
def vp2(n):
    if not n:return 1000
    return (abs(n)&-abs(n)).bit_length()-1
def dyad(Q):
    # Seek an F2-hyperplane on which both quadrics vanish as polynomials.
    for mask in range(1,16):
        j=(mask&-mask).bit_length()-1
        T=[list(r) for r in ident(4)]
        T[j][j]=2
        for k in range(4):
            if k!=j:T[j][k]=(mask>>k)&1
        T=tuple(tuple(F(a) for a in r) for r in T)
        V=sc(F(1,2),ident(2))
        Z=change_unsafe(V,Q,T)
        if all((A[i][j]*(1 if i==j else 2)).denominator==1 for A in Z for i,j in pairs):
            return V,T
    return None

def main():
    d0=json.loads((RAW/'EXACT-RELATIVE-TANGENT-LIFT.json').read_bytes())
    A=[]
    for (a,b,c,r,s,t) in d0['actual_degree2_lift_quadrics']:
        A.append(mat((a,b,0,0,c,0,0,r,s,t)))
    Q=tuple(A);Q0=Q
    ST=[]
    M=ident(2);N=ident(4)
    def go(V,T,name):
        nonlocal Q,M,N
        Q=change(V,Q,T);M=mm(V,M);N=mm(N,T)
        ST.append((name,str(det(V)*det(T))))
    no=ident(2)
    x,y,u=d0['negative_seeds'][0]
    r=p*y*pow(q*x,-1,u)%u
    go(no,block(((1,F(r,u)),(0,F(1,u))),0),"strip first conic seed divisor")
    X,Y,V=d0['negative_seeds'][1]
    w=V//3
    r=p*Y*pow(q*(X//3),-1,w)%w
    go(no,block(((1,F(r,w)),(0,F(1,3*w))),2),"strip second conic seed divisor")
    for P in (5,1861,114649):
        r=rootpair(Q,P,0)
        if r is not None:
            go(sc(F(1,P),no),block(shift_line(P,*r),0),f"common first line at {P}")
        else:
            go(sc(F(1,P),no),block(((P,0),(0,P)),0),f"flip-flop at {P}")
            r=rootpair(Q,P,2)
            assert r is not None,P
            go(sc(F(1,P),no),block(shift_line(P,*r),2),f"common second line at {P}")
    for attempt in range(2):
        Z=dyad(Q)
        if not Z:break
        go(*Z,"common plane at 2")
    assert change(M,Q0,N)==Q
    coeffs=[coeff(q) for q in Q]
    c4,c6,DIS=invs(pencil(*(hessian(q) for q in coeffs)))
    o4,o6,oD=16*13*d*d,-64*35*d**3,2**8*9*d**6
    r,rem=divmod(c4,o4);assert not rem
    L=isqrt(isqrt(r))
    assert L==1 and r==L**4 and c6==L**6*o6 and DIS==L**12*oD
    print(json.dumps(dict(d=d,residual_level=L,raw_coefficient_max=max(abs(x) for Q in d0['actual_degree2_lift_quadrics'] for x in Q),
          minimal_coefficient_max=max(abs(x) for Q in coeffs for x in Q),
          transformed_coefficients=coeffs,quadric_change_rows=[[str(x) for x in row] for row in M],
          variable_change_rows=[[str(x) for x in row] for row in N],operations=ST),
        indent=2,sort_keys=True))
if __name__=='__main__':main()
