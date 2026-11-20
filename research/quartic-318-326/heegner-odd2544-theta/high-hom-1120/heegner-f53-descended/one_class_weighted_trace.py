#!/usr/bin/env python3
"""All 288 fixed-Weil-phase unit branches of one actual class, not whole trace."""
from collections import defaultdict
from itertools import product
import hashlib
import json
from first_full_translate import *
import marked_t16_invariants as direct

def install_fast_inverse(M, modulus):
    """Exact modular polynomial Euclidean inverse, independent of bit powers."""
    old=M.F.__pow__
    def trim(A):
        while A and A[-1]==0:A.pop()
        return A
    def div(A,B):
        if len(A)<len(B):return [],A
        S=[0]*(len(A)-len(B)+1); A=list(A)
        z=pow(B[-1],-1,p)
        for i in reversed(range(len(S))):
            S[i]=a=A[i+len(B)-1]*z%p
            if a:
                for j,b in enumerate(B):A[i+j]=(A[i+j]-a*b)%p
        return trim(S),trim(A)
    def submul(A,Q,B):
        Z=A+[0]*max(0,len(Q)+len(B)-1-len(A))
        for i,a in enumerate(Q):
            if a:
                for j,b in enumerate(B):
                    if b:Z[i+j]=(Z[i+j]-a*b)%p
        return trim(Z)
    def go(a,n):
        if n!=-1:return old(a,n)
        assert a
        if len(a.v)==1:return M.F.of(pow(a.v[0],-1,p))
        A,B=modulus,list(a.v); X,Y=[],[1]
        while B:
            Q,R=div(A,B)
            A,B=B,R
            X,Y=Y,submul(X,Q,Y)
        assert len(A)==1
        t=pow(A[0],-1,p)
        return M.F.trim([t*c for c in X])
    M.F.__pow__=go

def line(A,P,Q,Z):
    x,y=P; X,Y=Q
    if x==X and y==-Y:return Z[0]-x,None
    if x==X:m=(3*x*x+A.A)/(2*y)
    else:m=(Y-y)/(X-x)
    W=A.add(P,Q)
    return (Z[1]-y-m*(Z[0]-x))/(Z[0]-W[0]),W
def miller(A,P,T,l):
    s,f=P,P[0]**0
    for bit in bin(l)[3:]:
        g,s=line(A,s,s,T)
        f=f*f*g
        if bit=='1':
            g,s=line(A,s,P,T)
            f*=g
    assert s is None
    return f
def weil(A,P,Q,l):
    v=-miller(A,P,Q,l)/miller(A,Q,P,l)
    assert v!=P[0]**0 and v**l==P[0]**0
    return v

def faster_odd_edge(M,A,G,l):
    """Same exact portable Vélu equations as first_full_translate, no Gaussian samples."""
    K=[M.one]; s=t=z=M.zero
    Q=G
    for i in range(1,(l+1)//2):
        assert Q is not None and A.contains(Q)
        x,y=Q
        K=[a+b for a,b in zip([(-x)*w for w in K]+[M.zero],[M.zero]+K)]
        s+=x
        t+=2*(3*x*x+A.A)
        z+=2*(5*x**3+3*A.A*x+2*A.B)
        Q=A.add(Q,G)
    assert A.mul(l,G) is None
    B=M.E(A.A-5*t,A.B-7*z); target=coeffs(B); src=coeffs(A)
    K=parse(D16,[x.subfield() for x in K])
    a,b=parse(D16,src); z=D16.zero; o=D16.one
    f=[b,a,z,o]; fp=D16.pder(f)
    d=(l-1)//2
    der=D16.pder
    mul,add,neg=D16.pprod,D16.padd,D16.pneg
    D=mul(K,K)
    H=add(mul(der(K),der(K)),neg(mul(der(der(K)),K)))
    N=add(add(mul([-2*read(D16,s.subfield()),D16.F.of(2*d+1)],D),
              times(4,mul(f,H))),times(-2,mul(mul(fp,der(K)),K)))
    return Morphism(src,target,N,D,o)

def chart_cache():
    K=D8.k
    square=defaultdict(list)
    for x in K:square[x*x].append(x)
    dual=defaultdict(list)
    for x in K:
        if not x:continue
        H=x**4+1
        for s in square[H*H+12*x**4]:
            y=(s+H)/2
            if not y:continue
            T=x-2+3*x/y; U=(y-1)/x-2
            dual[T,U].append((x,y))
    def finite(T):
        for c in [2,4,16]:
            if not T+c:return False
            T=T*T/(T+c)
        return bool(T) # if t2=0, j has a pole, since p≠2
    for key,V in dual.items():
        if len(V)>1:assert any(not finite(T) for T in key)
    return {key:V[0] for key,V in dual.items() if all(finite(T) for T in key)}

def based(x,y):
    r=(x-1/x)/2; s=(2*y-x**4-1)/(4*x*x)
    assert s*s==r**4+r*r+1
    if r:
        A0=(s+1)/(r*r); B0=(A0*A0-1)*r
        X,Y=2*A0+1,2*B0
    elif s==D8.one:
        return (D8.F.of(3),D8.zero)
    else:
        X,Y=D8.zero,D8.zero
    if (X,Y)==(D8.F.of(3),D8.zero):return None
    # Add (3,0) directly on literal y²=x³−2x²−3x.
    z=Y/(X-3)
    rx=z*z-X-1; ry=z*(X-rx)-Y
    assert ry*ry==rx*(rx+1)*(rx-3)
    return rx,ry

def low_value(A,g16,g3,charts):
    U,f=A.quotient(g3,3)
    T,V=direct.t16(A,g16),direct.t16(U,f(g16))
    return based(*charts[T,V]),(T,V)

def dump_k(P):return [x.subfield() for x in P] if P else None
def short(P):return (P[0]-D8.F.of(2)/3,P[1]) if P else None
def long(P):return (P[0]+D8.F.of(2)/3,P[1]) if P else None
def leg(u,l):return 1 if pow(u,(l-1)//2,l)==1 else -1

def run():
    install_fast_inverse(D8,[-2]+[0]*7+[1])
    install_fast_inverse(D16,[-2]+[0]*15+[1])
    install_fast_inverse(D18,[1]+[0]*8+[-50]+[0]*8+[1])
    M17=faster_odd_edge(D16,D16.E0,D16.generator(17,17),17)
    M19=faster_odd_edge(D18,E(D18,M17.dst),M17.at(D18)(D18.generator(19,19)),19)
    B=M19.dst; B16=E(D16,B); B18=E(D18,B)
    _,num,den=D16.descended_action(D16.E0,lambda P:map_point(D16,[M17,M19],P),B16)
    Omega=Morphism(B,B,num,den,(1+D16.u)/2)
    P17,Q17=mix(D16,B,17,Omega); P19,Q19=mix(D18,B,19,Omega)
    z17=weil(B16,P17,Q17,17); z19=weil(B18,P19,Q19,19)
    assert weil(B16,B16.mul(3,P17),Q17,17)==z17**3
    assert weil(B18,B18.mul(3,P19),Q19,19)==z19**3
    g16,g3=[map_point(D8,[M17,M19],D8.generator(n,l)) for n,l in [(16,2),(3,3)]]
    charts=chart_cache()
    Aout=D8.E(-D8.F.of(13)/3,-D8.F.of(70)/27)
    S=None; rows=[]
    for a in range(1,17):
        T17=faster_odd_edge(D16,B16,B16.add(B16.mul(a,P17),Q17),17)
        A18=E(D18,T17.dst)
        f=T17.at(D18)
        P19t,Q19t=f(P19),f(Q19)
        assert weil(A18,P19t,Q19t,19)==z19**17
        f=T17.at(D8)
        g16t,g3t=f(g16),f(g3)
        for b in range(1,19):
            T19=faster_odd_edge(D18,A18,A18.add(A18.mul(b,P19t),Q19t),19)
            f=T19.at(D8)
            point,key=low_value(E(D8,T19.dst),f(g16t),f(g3t),charts)
            w=leg(a,17)*leg(b,19)
            S=Aout.add(S,Aout.mul(w,short(point)))
            rows.append(dict(a17=a,a19=b,w=w,t16=dump_k(key),phi=dump_k(point)))
    assert len(rows)==288
    assert rows[0]['phi']==[[27,16],[25,1]]
    dump={
      'stage':'one fixed oriented CM row, 288 exact low-level values',
      'B':B,'pairing17_field16':z17.v,'pairing19_field18':z19.v,
      'chart_usable_points':len(charts),'raw_weighted_sum':dump_k(long(S)),
      'additional_raw_order13_test':dump_k(long(Aout.mul(224,S))),
      'rows':rows}
    print(json.dumps(dump,indent=2,sort_keys=True))

if __name__=='__main__':run()
